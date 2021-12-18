#include "precompiled.hpp"
#include "libadt/vectset.hpp"
#include "opto/block.hpp"
#include "opto/cfgnode.hpp"
#include "opto/rootnode.hpp"
#include "opto/callnode.hpp"
#include "opto/compile.hpp"
#include "opto/addnode.hpp"
#include "opto/type.hpp"
#include "opto/graphKit.hpp"
#include "gc/shared/barrierSet.hpp"
#include "gc/shared/c2/barrierSetC2.hpp"
#include "opto/partialEscape.hpp"

VirtualState* VirtualState::clone() {
  VirtualState* new_st = new VirtualState(this->_entries_cnt);
  for (int i = 0; i < this->_entries_cnt; i++) {
    new_st->_entries[i] = this->_entries[i];
  }
  new_st->_lock_cnt = this->_lock_cnt;
  return new_st;
}

bool VirtualState::equals(VirtualState* vs) {
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

BlockState::BlockState() : _aliases(new Dict(cmpkey, hashkey)),
  _alloc_states(new Dict(cmpkey, hashkey)) {
#ifdef ASSERT
  _cfg = NULL;
  _block = NULL;
  _changed = false;
#endif 
}

BlockState::BlockState(Block* block) : _aliases(new Dict(cmpkey, hashkey)),
  _alloc_states(new Dict(cmpkey, hashkey)) {
#ifdef ASSERT
  assert(block != NULL, "must be");
  _cfg = NULL;
  _block = block;
  _changed = false;
#endif
}

BlockState::BlockState(PhaseSimpleCFG* cfg, Block* block) : _aliases(new Dict(cmpkey, hashkey)),
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
  for (AliasStateIter iter(this->_aliases); iter.has_next(); iter.next()) {
    Node* key = iter.key();
    Node* value = iter.value();
    bs->add_alias(key, value);
  }
  for (AllocStateIter iter(this->_alloc_states); iter.has_next(); iter.next()) {
    VirtualAllocNode* key = iter.key();
    AllocState* value = iter.value();
    bs->add_alloc_state(key, value->clone());
  }
  assert(bs->_aliases->Size() == this->_aliases->Size(), "clone is incomplete");
  assert(bs->_alloc_states->Size() == this->_alloc_states->Size(), "clone is incomplete");
  return bs;
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
    tty->print_cr("Alias -> VirtualAlloc:");
    for (AliasStateIter iter(this->_aliases); iter.has_next(); iter.next()) {
      const Node* key = iter.key();
      const Node* value = iter.value();
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
    tty->print_cr("VirtualAlloc -> AllocState:");
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

PhasePartialEA::PhasePartialEA(PhaseIterGVN *igvn) :
  Phase(PartialEA),
  _cfg(NULL),
  _igvn(igvn),
  _merge_point(NULL),
  _has_allocation(false) {
  assert(DoPartialEscapeAnalysis, "insane");
}

void PhasePartialEA::materialize(VirtualAllocNode* valloc, BlockState* bstate, bool* has_materialization) {
#ifdef ASSERT
  if (TracePartialEscapeAnalysis) {
    tty->print_cr("== Materialize virtual allocation N%d", valloc->_idx);
    tty->print("  ");
    valloc->dump();
  }
#endif
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
#ifdef ASSERT
  if (identical) {
    assert(false, "all fields in predecessor are same, why merging?");
  }
#endif
  return phi;
}

// Merge multi VirtualStates with the same VirtualAllocNode
void PhasePartialEA::merge_fields(GrowableArray<BlockState*>* pred_bstates, BlockState* merged_bstate, Node* alias_key_node) {
  VirtualAllocNode* alloc0 = pred_bstates->at(0)->get_alias(alias_key_node)->as_VirtualAlloc();
  VirtualState* vs0 = pred_bstates->at(0)->get_alloc_state(alloc0)->as_VirtualState();

  bool all_identical = true;
  for (int j = 1; j < pred_bstates->length(); j++) {
    Node* alloc_tmp = pred_bstates->at(j)->get_alias(alias_key_node);
#ifdef ASSERT
    assert(alloc_tmp == alloc0, "must be");
#endif
    VirtualState* vs_tmp = pred_bstates->at(j)->get_alloc_state(alloc0)->as_VirtualState();
    if (!vs_tmp->equals(vs0)) {
      all_identical = false;
      break;
    }
  }

  // If all field values are identical, this value will be the value of the field in
  // the new VirtualState.
  if (all_identical) {
    merged_bstate->add_alias(alias_key_node, alloc0);
    merged_bstate->add_alloc_state(alloc0, vs0->clone());
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
      VirtualState* vs_tmp = pred_bstates->at(pred_i)->get_alloc_state(alloc0)->as_VirtualState();
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
        merge_fields(pred_bstates, merged_bstate, field);
      }
      // Same trivial fields, that's pretty fine, the merged field will not change
      merged_vs->set_field(field_i, field);
      continue;
    }
    // Otherwise, this field is different in some predecessor,
    // create a phi node to merge these different nodes
    PhiNode* phi = create_phi_for_field(pred_bstates, alloc0, field, field_i);
    merged_vs->set_field(field_i, phi);
  }
  // All fields were processed, add alias and merged virtual state into block state
  merged_bstate->add_alias(alias_key_node, alloc0);
  merged_bstate->add_alloc_state(alloc0, merged_vs);
}

void PhasePartialEA::merge_phi(GrowableArray<BlockState*>* pred_bstates, BlockState* merged_bstate,
                               PhiNode* phi, bool* has_materialization) {
  assert((uint)pred_bstates->length() == phi->req() - 1/*RegionNode*/, "must match");
  bool all_identical = true;
  VirtualAllocNode* identical_virt = NULL;
  // First iteration, check if all inputs of Phi are aliased to the same VirtualAllocNode
  for (uint i = PhiNode::Input; i < phi->req(); i++) {
    Node* in = phi->in(i);
    Node* alias = pred_bstates->at(i - PhiNode::Input)->get_alias(in);
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
    merged_bstate->add_alias(phi, identical_virt);
  } else {
    // either some inputs are virtual, or escape
   for (uint j = PhiNode::Input; j < phi->req(); j++) {
      Node* in = phi->in(j);
      Node* alias = pred_bstates->at(j - PhiNode::Input)->get_alias(in);
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

  // Create intersection of alias nodes, VirtualAllocNode alives only if it exists
  // in all predecessors and has at least one common alias
  GrowableArray<Node*> alias_intersect;
  BlockState* bs = pred_bstates->at(0);
  for (AliasStateIter iter(bs->get_aliases()); iter.has_next(); iter.next()) {
    Node* key_node = iter.key();
    bool all_exist = true;
    for (int k = 1; k < pred_bstates->length(); k++) {
      Node* value_node = pred_bstates->at(k)->get_alias(key_node);
      if (value_node == NULL || !value_node->isa_VirtualAlloc()) { // alias is not exist
        all_exist = false;
        break;
      }
    }
    if (all_exist) {
      alias_intersect.append(key_node);
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
    for (int i = 0; i < alias_intersect.length(); i++) {
      Node* node = alias_intersect.at(i);
      int escaped_cnt = 0;
      for (int k = 0; k < pred_bstates->length(); k++) {
        VirtualAllocNode* alloc_node = pred_bstates->at(k)->get_alias(node)->as_VirtualAlloc();
        AllocState* st  = pred_bstates->at(k)->get_alloc_state(alloc_node);
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
        merge_fields(pred_bstates, merged_bstate, node);
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

#ifdef ASSERT
  // Verify correctness of merged block state
  assert(merged_bstate->get_aliases()->Size() >= (uint)alias_intersect.length(), "new graph state is incomplete");
  for (AliasStateIter iter(merged_bstate->get_aliases()); iter.has_next(); iter.next()) {
    Node* key = iter.key();
    VirtualAllocNode* value = iter.value()->as_VirtualAlloc();
    assert(key != NULL, "must be");
    assert(value != NULL, "must be");
  }
  for (AllocStateIter iter(merged_bstate->get_alloc_states()); iter.has_next(); iter.next()) {
    VirtualAllocNode* key = iter.key();
    AllocState* value = iter.value();
    assert(key != NULL, "must be");
    assert(value != NULL, "must be");
  }
#endif
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

      Node* alloc_alias = bstate->get_alias(alloc);
      if (alloc_alias->isa_VirtualAlloc()) {
        AllocState* alloc_st = bstate->get_alloc_state(alloc_alias->as_VirtualAlloc());
        assert(alloc_st->is_virtual_state(), "why not");
        Node* rhs = n->in(MemNode::ValueIn);
        Node* rhs_valloc = bstate->get_alias(rhs);
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

      Node* alloc_alias = bstate->get_alias(alloc);
      if(alloc_alias->isa_VirtualAlloc()) {
        AllocState* alloc_st = bstate->get_alloc_state(alloc_alias->as_VirtualAlloc());
        assert(alloc_st->is_virtual_state(), "why not");
        Node* nf = alloc_st->as_VirtualState()->get_field(nth);
        bstate->add_alias(n, nf);
        // todo: delete current node
        bstate->add_effect(NULL);
      } else {
        // todo:xxxs
      }
    }
  }
}

void PhasePartialEA::do_node(BlockState* bstate, Node* n) {
  switch(n->Opcode()) {
    // Instance Creation
    case Op_Allocate: {
      const TypeKlassPtr* klass_ptrtype = _igvn->type(n->as_Allocate()->in(AllocateNode::KlassNode))->is_klassptr();
      ciInstanceKlass* klass = klass_ptrtype->klass()->as_instance_klass();
      int nof_fields = klass->nof_nonstatic_fields();
      VirtualState* alloc_st = new (C->comp_arena()) VirtualState(nof_fields);
      VirtualAllocNode* alloc = new VirtualAllocNode(n, klass);
      bstate->add_alloc_state(alloc, alloc_st);
      bstate->add_alias(n, alloc);
      _igvn->register_new_node_with_optimizer(alloc);
      _has_allocation = true;
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
        bstate->add_alias(n, alloc);
      } else {
        // materialization
      }
      _has_allocation = true;
      break;
    }
    case Op_Proj: {
      Node* in = n->in(0);
      // rawoop proj of allocation
      if (in->isa_Allocate() && n->as_Proj()->_con == TypeFunc::Parms) {
        VirtualAllocNode* valloc = bstate->get_alias(in)->as_VirtualAlloc();
        bstate->add_alias(n, valloc);
      }
      break;
    }
    case Op_CheckCastPP: {
      Node* oop_in = n->in(1);
      // javaoop of allocation
      if (oop_in->isa_Proj() && oop_in->as_Proj()->_con == TypeFunc::Parms) {
        VirtualAllocNode* valloc = bstate->get_alias(oop_in)->as_VirtualAlloc();
        bstate->add_alias(n, valloc);
      }
      break;
    }
    case Op_EncodeP: {
      Node* narrow_oop_in = n->in(1);
      if (narrow_oop_in->isa_CheckCastPP()) {
        VirtualAllocNode* valloc = bstate->get_alias(narrow_oop_in)->as_VirtualAlloc();
        bstate->add_alias(n, valloc);
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
  Block_List visited;
  Block_Queue queue;
  queue.push_back(cfg.get_root_block());
  while (!queue.is_empty()) {
    Block *b = queue.pop_front();
    if (!visited.contains(b)) {
#ifdef ASSERT
      if (TracePartialEscapeAnalysis) {
        tty->print_cr("== Processing block B%d(pred: %d, succ:%d)", b->_pre_order, b->num_preds() - 1, b->_num_succs);
        tty->print("   Visited: [");
        for (uint visited_i = 0; visited_i < visited.max(); visited_i++) {
          tty->print("B%d ", visited[visited_i]->_pre_order);
        }
        tty->print_cr("]");
        tty->print("   Queue: ");
        queue.print();
      }
#endif
      bool delay_visit = false;
      BlockState* bstate = NULL; // Initialize only when actually visiting
      uint num_preds = b->num_preds() - 1;// Unfortunately num_preds() is ONE based, substrate 1 to get real num
      // Process current block, special cases for CFG merge point or loop header block
      // Do not treat root block as merge point even if it has multi predecessors
      if (num_preds > 1 && b != cfg.get_root_block()) {
        // Must be CFG merge point
        if (b->_loop != NULL) {
          // If it's loop header block
          assert(false, "not implement");
        } else {
          // Normal merge, check if all predecessor are visited
          bool all_pred_visited = true;
          uint pred_i = 0;
          for(pred_i = 0; pred_i < num_preds; pred_i++) {
            if (!visited.contains(cfg.get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/)))) {
              all_pred_visited = false;
              break;
            }
          }
          if (all_pred_visited) {
            // Merge predecessor states before visiting it
            GrowableArray<BlockState*> bstates;
            for (pred_i = 0; pred_i < num_preds; pred_i++) {
              assert(has_block_state(cfg.get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/))),
                    "missing graph state for visited predecessor block");
              BlockState* bs = get_block_state(cfg.get_block_for_node(b->pred(pred_i + 1/*ONE BASED*/)));
              bstates.push(bs);
            }
            set_merge_point(b->head()->as_Region());
            bstate = merge_block_states(&bstates);
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
      // Process its successor blocks, push them into pending queue, propagate current graph
      // state or clone it for successors. If current blosk is marked as delayed, stop propatating
      // its block state to successor, because there is no valid block state for itself.
      if (!delay_visit) {
        assert(visited.contains(b), "block was not visited");
        if (b->_num_succs == 1) {
          assert(b->_succs[0] != NULL, "sanity check");
          assert(bstate != NULL, " propagate null block state to successor");
          if (!has_block_state(b->_succs[0])) {
            NOT_PRODUCT( bstate->set_changed(false); )
            add_block_state(b->_succs[0], bstate); // Associate block state even if the block is not visited yet
          }
          queue.push_back(b->_succs[0]);
        } else {
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
    }
  }
#ifdef ASSERT
  assert(cfg.number_of_blocks() == visited._cnt, "some blocks are not visited yet");
  visited.reset();
  queue.reset();
  queue.push_back(cfg.get_root_block());
  while (!queue.is_empty()) {
    Block *b = queue.pop_front();
    if (!visited.contains(b)) {
      visited.push(b);
      assert(get_block_state(b) != NULL, "all block should have associate BlockState");
      for (uint i = 0; i < b->_num_succs; i++) {
        queue.push_back(b->_succs[i]);
      }
    }
  }
#endif
}
