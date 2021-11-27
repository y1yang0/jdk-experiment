// Author: Yi Yang
// The code does not allow any kind of distribution, all right reserved.

#include "precompiled.hpp"
#include "libadt/vectset.hpp"
#include "opto/block.hpp"
#include "opto/cfgnode.hpp"
#include "memory/allocation.hpp"
#include "opto/rootnode.hpp"
#include "opto/callnode.hpp"
#include "opto/compile.hpp"
#include "opto/addnode.hpp"
#include "opto/type.hpp"
#include "opto/graphKit.hpp"
#include "gc/shared/barrierSet.hpp"
#include "gc/shared/c2/barrierSetC2.hpp"
#include "opto/partialEscape.hpp"

// Utilities methods to facilitate use of Dict structure
// Used to iterate _aliases and _alloc_states, e.g.
// for (AliasStateIter iter(_aliases); iter.has_next(); iter.next()) {
//   ... = iter.key();
//   ... = iter.value();
// }
//
template<typename K, typename V>
class StateIter : public DictI {
public:
  StateIter(Dict* d) : DictI(d) {}
  bool has_next() { return test(); }
  void next()     { this->operator++(); }
  K key()         { return (K)this->_key; }
  V value()       { return (V)this->_value; }
};

using AliasStateIter = StateIter<Node*, Node*>;
using AllocStateIter = StateIter<VirtualAllocNode*, AllocState*>;

VirtualState* VirtualState::clone() {
  VirtualState* new_st = new VirtualState(this->_entries_cnt);
  for (int i = 0; i < this->_entries_cnt; i++) {
    new_st->_entries[i] = this->_entries[i];
  }
  new_st->_lock_cnt = this->_lock_cnt;
  return new_st;
}

bool VirtualState::equals(AllocState* as) {
  if (as->is_escaped_state()) {
    return false;
  }
  VirtualState* vs = as->as_VirtualState();
  if (vs->_entries_cnt != this->_entries_cnt) {
    return false;
  }
  if (vs->_lock_cnt != this->_lock_cnt) {
    return false;
  }
  for (int i = 0; i < this->_entries_cnt; i++) {
    if (vs->_entries[i] != this->_entries[i]) {
      return false;
    }
  }
  return true;
}

EscapedState* EscapedState::clone() {
  EscapedState* new_st = new EscapedState(this->_real_alloc->clone());
  return new_st;
}

BlockState::BlockState() :
  _alloc_states(new Dict(cmpkey, hashkey)) {
#ifdef ASSERT
  _cfg = NULL;
  _block = NULL;
  _changed = false;
#endif 
}

BlockState::BlockState(Block* block) :
  _alloc_states(new Dict(cmpkey, hashkey)) {
#ifdef ASSERT
  assert(block != NULL, "must be");
  _cfg = NULL;
  _block = block;
  _changed = false;
#endif
}

BlockState::BlockState(PhaseSimpleCFG* cfg, Block* block) :
  _alloc_states(new Dict(cmpkey, hashkey)) {
#ifdef ASSERT
  assert(cfg != NULL, "must be");
  assert(block != NULL, "must be");
  _cfg = cfg;
  _block = block;
  _changed = false;
#endif
}

BlockState* BlockState::clone() {
  BlockState* bs = new BlockState();
  for (AllocStateIter iter(this->_alloc_states); iter.has_next(); iter.next()) {
    VirtualAllocNode* key = iter.key();
    AllocState* value = iter.value();
    bs->add_alloc_state(key, value->clone());
  }
  assert(bs->_alloc_states->Size() == this->_alloc_states->Size(), "clone is incomplete");
  return bs;
}

bool BlockState::equals(BlockState* bs) {
  for (AllocStateIter iter(this->_alloc_states); iter.has_next(); iter.next()) {
    VirtualAllocNode* key = iter.key();
    AllocState* value = iter.value();
    AllocState* vs_value = bs->get_alloc_state(key);
    if (vs_value == NULL || !vs_value->equals(value)) {
      return false;
    }
  }
  return true;
}

#ifndef PRODUCT
void EscapedState::dump() const {
  tty->print("Materialized == ");
  _real_alloc->dump();
}

void VirtualState::dump() const {
  for (int i = 0; i < _entries_cnt; i++) {
    tty->print(" F%d : ", i);
    const Node* n = _entries[i];
    if (n == NULL) {
      tty->print_cr(" NULL");
    } else {
      n->dump();
    }
  }
}

void BlockState::verify() {
  for (AllocStateIter iter(_alloc_states); iter.has_next(); iter.next()) {
    VirtualAllocNode* key = iter.key();
    AllocState* value = iter.value();
    assert(key != NULL, "must be");
    assert(value != NULL, "must be");
  }
}

void BlockState::dump() {
  // Print associated basic block if possible...
  if (_block != NULL) {
    tty->print("===B%d", _block->_pre_order);
    // Print predecessors if possible...
    if (_cfg != NULL) {
      int real_pred = _block->num_preds() - 1/*ONE_BASED*/;
      if (real_pred > 0) {
        tty->print("(");
        for (int i = 0; i < real_pred; i++) {
          Block* pred_b = _cfg->get_block_for_node(_block->pred(i + 1/*ONE BASED*/));
          tty->print("B%d ", pred_b->_pre_order);
        }
        tty->print(")");
      }
    }
    tty->print_cr("BlockState(" INTPTR_FORMAT ")===", p2i(this));
  } else {
    tty->print_cr("===BlockState(" INTPTR_FORMAT ")===", p2i(this));
  }
  if (_changed || Verbose || WizardMode) {
    // Ignore BlockState detailed content if nothing changed after inherted from last block state
    for (AllocStateIter iter(this->_alloc_states); iter.has_next(); iter.next()) {
      const VirtualAllocNode* key = iter.key();
      const AllocState* value = iter.value();
      if (key != NULL) {
        key->dump();
      } else {
        tty->print_cr("NULL_KEY");
      }
      if (value != NULL) {
        value->dump();
      } else {
        tty->print_cr("NULL_VALUE");
      }
    }
  }
}
#endif

#ifdef ASSERT
static void trace_revisit_loop_header(Block* b) {
  ResourceMark rm;
  if (TracePartialEscapeAnalysis) {
    tty->print_cr("== Revisit loop header block B%d(pred: %d, succ:%d)", b->_pre_order, b->num_preds() - 1, b->_num_succs);
    tty->print_cr("   Loop: %d(depth:%d)", b->_loop->id(), b->_loop->depth());
    tty->print_cr("   Loop header: B%d", b->_loop->head()->_pre_order);
    tty->print("   Loop exit: [");
    GrowableArray<BlockProbPair>* exits = b->_loop->get_exits();
    for (int exit_i = 0; exit_i < exits->length(); exit_i++) {
      Block* exit_b = exits->adr_at(exit_i)->get_target();
      tty->print("B%d ", exit_b->_pre_order);
    }
    tty->print_cr("]");
  }
}

static void trace_process_block(Block *b, Block_List* visited, Block_Queue* queue, Block_List* loop_exit_blocks) {
  ResourceMark rm;
  if (TracePartialEscapeAnalysis) {
    tty->print("== Process block B%d(pred: %d, succ:%d)", b->_pre_order, b->num_preds() - 1, b->_num_succs);
    if (loop_exit_blocks->contains(b)) {
        tty->print_cr(" loop_exit");
    } else if (b->in_real_loop()) {
      if (b->is_loop_header()) {
        tty->print_cr(" loop_header");
      } else {
        tty->print_cr(" in_loop");
      }
    } else {
      tty->print_cr("");
    }
    tty->print("   Visited: [");
    for (uint visited_i = 0; visited_i < visited->max(); visited_i++) {
      tty->print("B%d ", visited->lookup(visited_i)->_pre_order);
    }
    tty->print_cr("]");
    tty->print("   Queue: ");
    queue->print();
  }
}

static void trace_materialize_virtuall_allocation(VirtualAllocNode* valloc) {
  if (TracePartialEscapeAnalysis) {
    tty->print_cr("== Materialize virtual allocation N%d", valloc->_idx);
    tty->print("  ");
    valloc->dump();
  }
}

#endif

PhasePartialEA::PhasePartialEA(PhaseIterGVN *igvn) :
  Phase(PartialEA),
  _cfg(NULL),
  _igvn(igvn),
  _merge_point(NULL),
  _has_allocation(false),
  _aliases(new Dict(cmpkey, hashkey)),
  _initial_loop_states(new (ResourceObj::C_HEAP, mtCompiler)GrowableArray<BlockState*>(0, mtCompiler)) {
  assert(DoPartialEscapeAnalysis, "insane");
}

bool PhasePartialEA::is_visited_all_preds(Block* b, Block_List* visited) {
  bool all_pred_visited = true;
  uint num_preds = b->num_preds() - 1;// Unfortunately num_preds() is ONE based, substrate 1 to get real num
  for (uint pred_i = 0; pred_i < num_preds; pred_i++) {
    if (!visited->contains(_cfg->get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/)))) {
      all_pred_visited = false;
      break;
    }
  }
  return all_pred_visited;
}

void PhasePartialEA::collect_pred_block_states(Block* b, GrowableArray<BlockState*>* bstates) {
  uint num_preds = b->num_preds() - 1;// Unfortunately num_preds() is ONE based, substrate 1 to get real num
  for (uintx pred_i = 0; pred_i < num_preds; pred_i++) {
    assert(has_block_state(_cfg->get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/))),
          "missing graph state for visited predecessor block");
    BlockState* bs = get_block_state(_cfg->get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/)));
    bstates->push(bs);
  }
}

void PhasePartialEA::materialize(VirtualAllocNode* valloc, BlockState* bstate, bool* has_materialization) {
  NOT_PRODUCT( trace_materialize_virtuall_allocation(valloc) );
  // I think we already misuse the following pattern in other places.
  C->for_igvn()->clear();
  C->initial_gvn()->replace_with(_igvn);
  JVMState* jvms = C->clone_jvms(valloc->in(1)->as_SafePoint());
  GraphKit kit(jvms);
  ciKlass* kls = valloc->get_klass();
  Node* kls_node = kit.makecon(TypeKlassPtr::make(kls));
  Node* real_alloc = kit.new_instance(kls_node);
  EscapedState* es = new EscapedState(real_alloc);
  bstate->del_alloc_state(valloc);
  bstate->add_alloc_state(valloc, es);
  if (kit.has_exceptions()) {
    C->rethrow_exceptions(kit.transfer_exceptions_into_jvms());
  }
  *has_materialization = true;
}

// Find all nth fields from predecessor block state, wire them into newly created PhiNode
PhiNode* PhasePartialEA::create_phi_for_field(GrowableArray<BlockState*>* pred_bstates, VirtualAllocNode* valloc,
                                              Node* field, int field_idx) {
  assert(pred_bstates->length() >= 2, "must be");
#ifdef ASSERT
  bool identical = true;
#endif
  int phi_idx = 1;
  const Type* phi_type = field != NULL ? _igvn->type(field) : Type::BOTTOM;
  //fixme:meet field and others
  PhiNode* phi = new PhiNode(get_merge_point(), phi_type);
  phi->init_req(phi_idx++, field != NULL ? field : C->top());
  for (int pred_i = 1; pred_i < pred_bstates->length(); pred_i++) {
    VirtualState* vs_tmp = pred_bstates->at(pred_i)->get_alloc_state(valloc)->as_VirtualState();
    Node* field_tmp = vs_tmp->get_field(field_idx);
    // TODO: if field_tmp == NULL, it means this field is not initialized, I think we 
    // should use default node instead of null, i.e. Con(1) for int field, Con(1.0) for double,
    if (field_tmp == NULL) {
      phi->init_req(phi_idx++, C->top());
    } else {
      phi->init_req(phi_idx++, field_tmp);
    }
#ifdef ASSERT
    if (field != field_tmp) {
      identical = false;
    }
#endif
  }
  _igvn->register_new_node_with_optimizer(phi);
  Node* exist_phi = _igvn->hash_find_insert(phi);
#ifdef ASSERT
  if (identical) {
    assert(false, "all fields in predecessor are same, why merging?");
  }
#endif
  return exist_phi == NULL ? phi : (PhiNode*)exist_phi;
}

// Merge multi VirtualStates with the same VirtualAllocNode
void PhasePartialEA::merge_fields(GrowableArray<BlockState*>* pred_bstates, BlockState* merged_bstate, VirtualAllocNode* valloc) {
  assert(pred_bstates->length() >= 2, "must be");
  assert(merged_bstate != NULL, "merged BlockState is not created yet");
  assert(valloc != NULL, "invalid VirtualAllocNode");
  VirtualState* vs0 = pred_bstates->at(0)->get_alloc_state(valloc)->as_VirtualState();

  bool all_identical = true;
  for (int j = 1; j < pred_bstates->length(); j++) {
    VirtualState* vs_tmp = pred_bstates->at(j)->get_alloc_state(valloc)->as_VirtualState();
    if (!vs_tmp->equals(vs0)) {
      all_identical = false;
      break;
    }
  }

  // If all field values are identical, this value will be the value of the field in
  // the new VirtualState.
  if (all_identical) {
    merged_bstate->add_alloc_state(valloc, vs0->clone());
    return;
  }

  // If some field values differ, creates a new Phi node for this field. If a field
  // that should be merged references a virtual object (i.e., a VirtualAlloc node with
  // a VirtualState), this object needs to be materialized before merging.
  VirtualState* merged_vs = new VirtualState(vs0->nof_field());
  for (int field_i = 0; field_i < vs0->nof_field(); field_i++) { // for each field
    Node* field = vs0->get_field(field_i);

    bool same_field = true;
    for (int pred_i = 1; pred_i < pred_bstates->length(); pred_i++) {
      VirtualState* vs_tmp = pred_bstates->at(pred_i)->get_alloc_state(valloc)->as_VirtualState();
      Node* pred_field = vs_tmp->get_field(field_i);
      if (pred_field != field) {
        same_field = false;
        break;
      }
    }
    // If this field is the same in all predecessor block state
    if (same_field) {
      // Same fields, but refer to another VirtualAlloc, apply merge_fields recursively
      if (field != NULL && field->isa_VirtualAlloc()) {
        merge_fields(pred_bstates, merged_bstate, field->as_VirtualAlloc());
      }
      // Same trivial fields, that's pretty fine, the merged field will not change
      merged_vs->set_field(field_i, field);
      continue;
    }
    // Otherwise, this field is different in some predecessor,
    // create a phi node to merge these different nodes
    PhiNode* phi = create_phi_for_field(pred_bstates, valloc, field, field_i);
    merged_vs->set_field(field_i, phi);
  }
  // All fields were processed, add merged virtual state into block state
  merged_bstate->add_alloc_state(valloc, merged_vs);
}

void PhasePartialEA::merge_phi(GrowableArray<BlockState*>* pred_bstates, BlockState* merged_bstate,
                               PhiNode* phi, bool* has_materialization) {
  assert((uint)pred_bstates->length() == phi->req() - 1/*RegionNode*/, "must match");
  bool all_identical = true;
  VirtualAllocNode* identical_virt = NULL;
  // First iteration, check if all inputs of Phi are aliased to the same VirtualAllocNode
  for (uint i = PhiNode::Input; i < phi->req(); i++) {
    Node* in = phi->in(i);
    Node* alias = get_alias(in);
    if (alias != NULL && alias->isa_VirtualAlloc()) {
      if (identical_virt == NULL) {
        identical_virt = alias->as_VirtualAlloc();
      } else {
        if (alias->as_VirtualAlloc() != identical_virt) {
          all_identical = false;
          break;
        }
      }
    }
  }
  if (all_identical && identical_virt != NULL) {
    add_alias(phi, identical_virt);
  } else {
    // either some inputs are virtual, or escape
   for (uint j = PhiNode::Input; j < phi->req(); j++) {
      Node* in = phi->in(j);
      Node* alias = get_alias(in);
      if (alias != NULL && alias->isa_VirtualAlloc()) {
        AllocState* st = pred_bstates->at(j - PhiNode::Input)->get_alloc_state(alias->as_VirtualAlloc());
        if (st->is_escaped_state()) {
          assert(false, "todo");
        } else {
          assert(st->is_virtual_state(), "neither escaped nor virtual");
          materialize(alias->as_VirtualAlloc(), pred_bstates->at(j - PhiNode::Input), has_materialization);
        }
      }
    }
  }
}

// Merge multi state in predecessors, resulting in merged state, which will be used
// in CFG merge block
BlockState* PhasePartialEA::merge_block_states(GrowableArray<BlockState*>* pred_bstates) {
  assert(pred_bstates->length() >= 2, "sanity check");
  assert(get_merge_point() != NULL, "merge point node is not set");

  // Create intersection of VirtualAllocNode that exists in all predecessors and has at least one common alias
  GrowableArray<VirtualAllocNode*> valloc_intersect;
  BlockState* bs = pred_bstates->at(0);
  for (AllocStateIter iter(bs->get_alloc_states()); iter.has_next(); iter.next()) {
    VirtualAllocNode* key_node = iter.key();
    bool all_exist = true;
    for (int k = 1; k < pred_bstates->length(); k++) {
      AllocState* st = pred_bstates->at(k)->get_alloc_state(key_node);
      if (st == NULL) { // VirtualAlloc is not exist
        all_exist = false;
        break;
      }
    }
    if (all_exist) {
      valloc_intersect.append(key_node);
    }
  }
  // For each alias node, get corresponding VirtualAllocNode, looks at related
  // AllocState in all predecessors. If VirtualAllocNode escaped in all predecessors
  // the merged state for the node is EscapedState,new materialized points to Phi node
  // that merges all materialized node in predecessors. If VirtualAllocNode escaped in
  // some predecessors, materialize all virtual allocation, then process as previous
  // If VirtualAllocNode is not escaped in any predecessor, the merged state should also
  // be virtual. Specifically, if all fields are identical, they would be value of fields
  // in new state, otherwise, create Phi for these fields.
  bool has_materialization = false;
  BlockState* merged_bstate = new BlockState();
  do { // Run until meeting the fix point - no more materialization happens
    for (int i = 0; i < valloc_intersect.length(); i++) {
      VirtualAllocNode* valloc = valloc_intersect.at(i);
      int escaped_cnt = 0;
      for (int k = 0; k < pred_bstates->length(); k++) {
        AllocState* st  = pred_bstates->at(k)->get_alloc_state(valloc);
        if (st->is_escaped_state()) {
          escaped_cnt++;
        }
      }
      // Escaped in all predecessors
      if (escaped_cnt == pred_bstates->length()) {
        assert(false, "not implement");
      } else if (escaped_cnt > 0) {
        // Escaped in some predecessors
        assert(false, "not implement");
      } else {
        // Not escaped in all predecessors
        merge_fields(pred_bstates, merged_bstate, valloc);
      }
    }

    // Process Phi that assocates with merge point then
    for (DUIterator_Fast imax, i = get_merge_point()->fast_outs(imax); i < imax; i++) {
      Node* use = get_merge_point()->fast_out(i);
      if (use->is_Phi()) {   // Check for Phi users
        assert(use->in(0) == (Node*)get_merge_point(), "phi uses region only via in(0)");
        PhiNode* phi = use->as_Phi();
        merge_phi(pred_bstates, merged_bstate, phi, &has_materialization);
      }
    }

    if(has_materialization) {
      // TODO: invalidate previous assumptions about which objects are virtual

    }
  } while(has_materialization);

  // Verify correctness of merged block state
  NOT_PRODUCT( merged_bstate->verify(); )
  return merged_bstate;
}

void PhasePartialEA::do_store(BlockState* bstate, Node* n) {
  Node* adr = n->in(MemNode::Address);
  const Type *adr_type = _igvn->type(adr);
  adr_type = adr_type->make_ptr();
#ifdef ASSERT
  if (adr_type == NULL) {
    n->dump(1);
    assert(adr_type != NULL, "dead node should not be on list");
    return;
  }
#endif
  int opcode = n->Opcode();
  if (adr_type->isa_oopptr() || adr_type->isa_rawptr() && adr_type == TypeRawPtr::NOTNULL) {
    intptr_t off;
    AllocateNode* alloc = AllocateNode::Ideal_allocation(adr, _igvn, off);
    if (alloc != NULL) {
      Node* klass_node = alloc->in(AllocateNode::KlassNode);
      const TypeKlassPtr* klass_ptrtype = _igvn->type(klass_node)->is_klassptr();
      ciInstanceKlass* klass = klass_ptrtype->klass()->as_instance_klass();
      ciField* field = klass->get_field_by_offset(off, false);
      int nth = klass->nonstatic_field_nth(field);

      Node* alloc_alias = get_alias(alloc);
      if (alloc_alias->isa_VirtualAlloc()) {
        AllocState* alloc_st = bstate->get_alloc_state(alloc_alias->as_VirtualAlloc());
        assert(alloc_st->is_virtual_state(), "why not");
        Node* rhs = n->in(MemNode::ValueIn);
        Node* rhs_valloc = get_alias(rhs);
        if (rhs_valloc != NULL && rhs_valloc->isa_VirtualAlloc()) {
          alloc_st->as_VirtualState()->set_field(nth, rhs_valloc);
        } else {
          alloc_st->as_VirtualState()->set_field(nth, rhs);
        }
        // todo: delete current node
        bstate->add_effect(NULL);
      }
    }
  }
}

void PhasePartialEA::do_load(BlockState* bstate, Node* n) {
  Node* adr = n->in(MemNode::Address);
  const Type *adr_type = _igvn->type(adr);
  adr_type = adr_type->make_ptr();
#ifdef ASSERT
  if (adr_type == NULL) {
    n->dump(1);
    assert(adr_type != NULL, "dead node should not be on list");
    return;
  }
#endif
  int opcode = n->Opcode();
  if (adr_type->isa_oopptr() || adr_type->isa_rawptr() && adr_type == TypeRawPtr::NOTNULL) {
    intptr_t off;
    AllocateNode* alloc = AllocateNode::Ideal_allocation(adr, _igvn, off);
    if (alloc != NULL) {
      Node* klass_node = alloc->in(AllocateNode::KlassNode);
      const TypeKlassPtr* klass_ptrtype = _igvn->type(klass_node)->is_klassptr();
      ciInstanceKlass* klass = klass_ptrtype->klass()->as_instance_klass();
      ciField* field = klass->get_field_by_offset(off, false);
      int nth = klass->nonstatic_field_nth(field);

      Node* alloc_alias = get_alias(alloc);
      if(alloc_alias->isa_VirtualAlloc()) {
        AllocState* alloc_st = bstate->get_alloc_state(alloc_alias->as_VirtualAlloc());
        assert(alloc_st->is_virtual_state(), "why not");
        Node* nf = alloc_st->as_VirtualState()->get_field(nth);
        add_alias(n, nf);
        // todo: delete current node
        bstate->add_effect(NULL);
      } else {
        // todo:xxxs
      }
    }
  }
}

void PhasePartialEA::do_node(BlockState* bstate, Node* n) {
  if (get_alias(n) != NULL) {
    return;
  }
  switch(n->Opcode()) {
    // Instance Creation
    case Op_Allocate: {
      const TypeKlassPtr* klass_ptrtype = _igvn->type(n->as_Allocate()->in(AllocateNode::KlassNode))->is_klassptr();
      ciInstanceKlass* klass = klass_ptrtype->klass()->as_instance_klass();
      int nof_fields = klass->nof_nonstatic_fields();
      VirtualState* alloc_st = new (C->comp_arena()) VirtualState(nof_fields);
      VirtualAllocNode* alloc = new VirtualAllocNode(n, klass);
      bstate->add_alloc_state(alloc, alloc_st);
      add_alias(n, alloc);
      _igvn->register_new_node_with_optimizer(alloc);
      break;
    }
    // Array Creation
    case Op_AllocateArray: {
      Node* arr_len = n->as_AllocateArray()->in(AllocateNode::ALength);
      // Only array allocations with a statically known size can be processed by Partial
      // Escape Analysis.
      const TypeInt* arr_len_t = _igvn->type(arr_len)->is_int();
      if (arr_len_t->is_con() && arr_len_t->get_con() < PartialEAArrayAllocLimit) {
        const TypeKlassPtr* klass_ptrtype = _igvn->type(n->as_AllocateArray()->in(AllocateNode::KlassNode))->is_klassptr();
        VirtualState* alloc_st = new (C->comp_arena()) VirtualState(arr_len_t->get_con());
        VirtualAllocNode* alloc = new VirtualAllocNode(n, klass_ptrtype->klass());
        _igvn->register_new_node_with_optimizer(alloc);
        bstate->add_alloc_state(alloc, alloc_st);
        add_alias(n, alloc);
      } else {
        // materialization
      }
      break;
    }
    case Op_Proj: {
      Node* in = n->in(0);
      // rawoop proj of allocation
      if (in->isa_Allocate() && n->as_Proj()->_con == TypeFunc::Parms) {
        VirtualAllocNode* valloc = get_alias(in)->as_VirtualAlloc();
        add_alias(n, valloc);
      }
      break;
    }
    case Op_CheckCastPP: {
      Node* oop_in = n->in(1);
      // javaoop of allocation
      if (oop_in->isa_Proj() && oop_in->as_Proj()->_con == TypeFunc::Parms) {
        VirtualAllocNode* valloc = get_alias(oop_in)->as_VirtualAlloc();
        add_alias(n, valloc);
      }
      break;
    }
    case Op_EncodeP: {
      Node* narrow_oop_in = n->in(1);
      if (narrow_oop_in->isa_CheckCastPP()) {
        VirtualAllocNode* valloc = get_alias(narrow_oop_in)->as_VirtualAlloc();
        add_alias(n, valloc);
      }
      break;
    }
  }
  if (n->is_Store()) {
    do_store(bstate, n);
  }
  if (n->is_Load()) {
    do_load(bstate, n);
  }
}

void PhasePartialEA::do_block(BlockState* bstate, Block* b) {
  assert(b->head()->is_Region() || b->head()->is_Root() || b->head()->is_Start(),
        "start of block should be either region, root or start");
  for (uint i = 0; i < b->number_of_nodes(); i++) {
    do_node(bstate, b->get_node(i));
  }
}

void PhasePartialEA::do_analysis() {
  ResourceMark rm;
  log_info(partialea)("Start Partial Escape Analysis for %s", C->method()->name()->as_utf8());

  PhaseSimpleCFG cfg(C, _igvn);
  _cfg = & cfg;
#ifdef ASSERT
  if (DumpCFGDuringPEA) {
    cfg.dump();
  }
#endif
  // Traverse the CFG in reverse post order, in this way, all predecessor blocks were
  // visited before visiting a basic block, therefore I can merge predecessor block
  // states then propagate it further.
  GrowableArray<CFGLoop*> loop_verified; // Record processed loop
  Block_List loop_exit_blocks;           // Record loop exit blocks
  Block_List visited;                    // Record visited block
  Block_Queue queue;                     // Pending queue, analysis stops when all elements were drained from it
  queue.push_back(cfg.get_root_block());
  while (!queue.is_empty()) {
    Block *b = queue.pop_front();
    if (!visited.contains(b)) {
      NOT_PRODUCT( trace_process_block(b, &visited, &queue, &loop_exit_blocks) );

      bool delay_visit = false;
      BlockState* bstate = NULL; // Initialize only when actually visiting
      uint num_preds = b->num_preds() - 1;// Unfortunately num_preds() is ONE based, substrate 1 to get real num
      // Process loop exit blocks
      if (loop_exit_blocks.contains(b)) {
        // Delay processing loop exit blocks until speculative block state is verified
        bool exit_verified_loop = false;
        for (int loop_i = 0; loop_i < loop_verified.length(); loop_i++) {
          CFGLoop* the_loop = loop_verified.at(loop_i);
          if (the_loop->is_loop_exit(b)) {
            exit_verified_loop = true; // Find exit block from verified loop
            break;
          }
        }
        if (!exit_verified_loop) {
          delay_visit = true;
        }
      }
      if (!delay_visit) {
        if (num_preds > 1 && b != cfg.get_root_block()) { // Must be CFG merge point
          // Process current block, special cases for CFG merge point or loop header block
          // Do not treat root block as merge point even if it has multi predecessors
          // If it's loop header block and not visited yet?
          if (b->in_real_loop() && b->is_loop_header()) {
            // Record loop exit blocks
            GrowableArray<BlockProbPair>* exits = b->_loop->get_exits();
            for (int exit_i = 0; exit_i < exits->length(); exit_i++) {
              Block* exit_b = exits->adr_at(exit_i)->get_target();
              loop_exit_blocks.push(exit_b);
            }
            // Okay, save block state from the only vsiited precedessor block as
            // speculative block state. This speculative block state can be proved
            // to wrong if it mismatches to merged block states later, in such case,
            // I need to reprocess the whole loop.
            Block* visited_pred = NULL;
            for (uint pred_i = 0; pred_i < num_preds; pred_i++) {
              Block* pred_b = cfg.get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/));
              if (visited.contains(pred_b)) {
                if (visited_pred == NULL) {
                  visited_pred = pred_b;
                } else {
                  visited_pred = NULL;
                }
              }
            }
            guarantee(visited_pred != NULL, "expect only one predecessor was visited");
            assert(has_block_state(b), "loop header state is set");
            // Reprocessing the loop header block? Use merged block state
            if (_initial_loop_states->length() > 0 && get_block_state(b) == _initial_loop_states->last()) {
              bstate = _initial_loop_states->last();
            } else {
              // Otherwise, propagate predecessor block state and use it as initial speculative state
              bstate = get_block_state(visited_pred);
              _initial_loop_states->push(bstate);
            }
            // Walk nodes and mark as visited as usual
            do_block(bstate, b);
            visited.push(b);
          } else {
            // Normal merge, check if all predecessor are visited
            bool all_pred_visited = is_visited_all_preds(b, &visited);
            if (all_pred_visited) {
              // Merge predecessor states before visiting it
              GrowableArray<BlockState*> pred_bstates;
              collect_pred_block_states(b, &pred_bstates);
              set_merge_point(b->head()->as_Region());
              bstate = merge_block_states(&pred_bstates);
              // Visit it with merged graph state
              do_block(bstate, b);
              visited.push(b);
            } else {
              // Delay visiting current block until it's predecessor blocks are all visited
              delay_visit = true;
            }
          }
        } else {
          assert(num_preds == 1 || b == cfg.get_root_block(),
                "neither 0 predecessor nor root block? that's not reasonable");
          if (!has_block_state(b)) {
            bstate = create_block_state(b);
          } else {
            bstate = get_block_state(b);
          }
          do_block(bstate, b);
          visited.push(b);
        }
      }
      // Process its successor blocks, push them into pending queue, propagate current graph
      // state or clone it for successors. If current blosk is marked as delayed, stop propatating
      // its block state to successor, because there is no valid block state for itself.
      // For backedge block, i.e. block that connects to loop header block, do not anything
      // for it, because loop header block has its own special approach to process block state.
      if (!delay_visit) {
        assert(visited.contains(b), "block was not visited");
        if (b->_num_succs >= 1 &&
            b->_succs[0]->in_real_loop() &&
            b->_succs[0]->is_loop_header()) {
          // One successor that connects to loop header block
          Block* unique_succ = b->_succs[0];
          guarantee(b->_num_succs == 1, "must be");
          assert(unique_succ != NULL, "sanity check");
          assert(bstate != NULL, " propagate null block state to successor");
          if (visited.contains(unique_succ)) {
            // Backedge control flow
            assert(has_block_state(unique_succ), "loop header block from backedge must have block state");
            assert(!loop_verified.contains(unique_succ->_loop), "loop is being processing");
          } else {
            // Normal control flow
             assert(!has_block_state(unique_succ), "first time to visit loop header block");
             assert(!loop_verified.contains(unique_succ->_loop), "loop is being processing");
             NOT_PRODUCT( bstate->set_changed(false); )
             add_block_state(unique_succ, bstate);
          }
          queue.push_back(unique_succ); // Push it even if already visited
        } else if (b->_num_succs == 1) {
          // One successor
          assert(b->_succs[0] != NULL, "sanity check");
          assert(bstate != NULL, " propagate null block state to successor");
          if (!has_block_state(b->_succs[0])) {
            NOT_PRODUCT( bstate->set_changed(false); )
            add_block_state(b->_succs[0], bstate); // Associate block state even if the block is not visited yet
          }
          queue.push_back(b->_succs[0]);
        } else {
          // Multiple successors, CFG split point
          assert(b->_num_succs > 1, "0 successor? that's not reasonable");
          for (uint i = 0; i < b->_num_succs; i++) {
            BlockState* cloned_bs = bstate->clone();
            assert(cloned_bs != NULL, "propagate null block state to successor");
            add_block_state(b->_succs[i], cloned_bs); // Associate block state even if the block is not visited yet
            queue.push_back(b->_succs[i]);
          }
        }
#ifdef ASSERT
        bstate->set_cfg(&cfg);
        bstate->set_block(b);
        if (TracePartialEscapeAnalysis) {
          bstate->dump();
        }
#endif
      } else {
        assert(bstate == NULL, "BlockState should not exist");
        assert(!visited.contains(b), "delayed block was already visited");
        queue.push_back(b);
      }
    } else {
      assert(get_block_state(b) != NULL, "missing BlockState");
      // If it's loop header block and was already visited? Prove old assumption(speculative block state)
      if (b->in_real_loop() && b->is_loop_header()) {
        NOT_PRODUCT( trace_revisit_loop_header(b) );

        // Try to merge all backedge blocks
        GrowableArray<BlockState*> pred_bstates;
        collect_pred_block_states(b, &pred_bstates);
        set_merge_point(b->head()->as_Region());
        BlockState* merged_backedge_bs = merge_block_states(&pred_bstates);
        // Check if merged block state is equal to initial speculative block state
        BlockState* initial_speculative_bs = _initial_loop_states->last();
        // If so, it's able to visit loop exit blocks
        if (initial_speculative_bs->equals(merged_backedge_bs))  {
          // Pop speculative block state
          _initial_loop_states->pop();
          // Mark current loop as verified
          loop_verified.push(b->_loop);
          // Push all loop exit blocks into pending queue
          GrowableArray<BlockProbPair>* exits = b->_loop->get_exits();
          for (int exit_i = 0; exit_i < exits->length(); exit_i++) {
            Block* exit_b = exits->adr_at(exit_i)->get_target();
            queue.push_back(exit_b);
          }
        } else {
          // If not, reprocess the whole loop until reached fixed point

          // Remove all loop member blocks from visited set
          Block_List members;
          cfg.collect_loop_members(&members, b->_loop);
          for (uint member_i = 0; member_i < members.max(); member_i++) {
            for (uint visited_k = 0; visited_k < visited.max(); visited_k++) {
              if (visited[visited_k] == members[member_i]) {
                visited.remove(visited_k);
                break;
              }
            }
          }
          // Remove associated blocks states, loop exit blocks should be cleared as well
          for (uint member_i = 0; member_i < members.max(); member_i++) {
            Block* member_block = members[member_i];
            if (has_block_state(member_block)) {
              clear_block_state(member_block);
            }
            for (uint succ_i = 0; succ_i < member_block->_num_succs; succ_i++) {
              Block* succ_block = member_block->_succs[succ_i];
              if (has_block_state(succ_block)) {
                clear_block_state(succ_block);
              }
            }
          }
          // Use new state instead of initial speculative state
          _initial_loop_states->pop();
          _initial_loop_states->push(merged_backedge_bs);
          add_block_state(b, merged_backedge_bs); // block state of loop header was already cleared
          // Reprocess loop header block
          queue.push_back(b);
          guarantee(!visited.contains(b), "unable to reprocess loop header block");
        }
      }
    }
  }
  assert(queue.is_empty(), "leftover blocks in pending queue");
  assert(cfg.number_of_blocks() == visited._cnt, "some blocks are not visited yet");
  verify_block_states();

#ifndef PRODUCT
  if (TracePartialEscapeAnalysis) {
    tty->print_cr("===Alias Mapping===");
    for (AliasStateIter iter(this->_aliases); iter.has_next(); iter.next()) {
      const Node* key = iter.key();
      const Node* value = iter.value();
      key->dump();
      value->dump();
      tty->print_cr("");
    }
  }
#endif
}

void PhasePartialEA::verify_block_states() {
  Block_List visited;
  Block_Queue queue;
  queue.push_back(_cfg->get_root_block());
  while (!queue.is_empty()) {
    Block* b = queue.pop_front();
    if (!visited.contains(b)) {
      visited.push(b);
      BlockState* bstate = get_block_state(b);
      assert(bstate != NULL, "all blocks should have associate BlockState");
      bstate->verify();
      for (uint i = 0; i < b->_num_succs; i++) {
        queue.push_back(b->_succs[i]);
      }
    }
  }
}