#ifndef SHARE_OPTO_PARTIAL_ESCAPE_HPP
#define SHARE_OPTO_PARTIAL_ESCAPE_HPP

#include "opto/node.hpp"
#include "opto/cfgnode.hpp"
#include "opto/block.hpp"
#include "opto/phaseX.hpp"
#include "opto/opcodes.hpp"
#include "libadt/dict.hpp"
#include "utilities/growableArray.hpp"
#include "utilities/resourceHash.hpp"

// ==========PEA=========
// Each object allocation encountered in the original code is represented
// by a VirtualObject node. For each of these VirtualObject nodes there is
// an ObjectState describing the current knowledge about this allocation.
// If the allocation is still virtual,
// the state is a VirtualState representing the field values and the lock
// count. If the allocation escaped, the state is an EscapedState containing
// the materialized value.
class VirtualAllocNode : public Node {
private:
  ciKlass* _klass;
public:
  VirtualAllocNode(Node* n, ciKlass* klass): Node(0, n), _klass(klass) {
    init_class_id(Class_VirtualAlloc);
  }

  virtual int Opcode() const;
  ciKlass* get_klass() { return _klass; }
};

class VirtualState;
class EscapedState;

class AllocState : public ResourceObj {
public:
  virtual AllocState* clone() = 0;
  virtual bool is_virtual_state() = 0;
  virtual bool is_escaped_state() = 0;
  virtual VirtualState* as_VirtualState() = 0;
  virtual EscapedState* as_EscapedState() = 0;

#ifndef PRODUCT
  virtual void dump() const = 0;
#endif
};

class VirtualState : public AllocState {
private:
  int _lock_cnt;
  int _entries_cnt;
  Node** _entries;

public:
  VirtualState(int max_entries) : _lock_cnt(0),  _entries_cnt(max_entries) {
    _entries = NEW_RESOURCE_ARRAY(Node*, max_entries);
    for (int i = 0; i < _entries_cnt; i++) {
      _entries[i] = NULL;
    }
  }

  void set_field(int idx, Node* n) { assert(idx < _entries_cnt, "sanity check"); _entries[idx] = n; }
  Node* get_field(int idx) { assert(idx < _entries_cnt, "sanity check"); return _entries[idx]; }
  int nof_field() { return _entries_cnt; }

  bool equals(VirtualState* vs);

  virtual VirtualState* clone();
  virtual bool is_virtual_state() { return true; }
  virtual bool is_escaped_state() { return false; }
  virtual VirtualState* as_VirtualState()  { return this; }
  virtual EscapedState* as_EscapedState()  { return NULL; }

#ifndef PRODUCT
  virtual void dump() const;
#endif
};

class EscapedState : public AllocState {
private:
  Node* _real_alloc;
public:
  EscapedState(Node* real_alloc) : _real_alloc(real_alloc) {}

  virtual EscapedState* clone();
  virtual bool is_virtual_state() { return false; }
  virtual bool is_escaped_state() { return true; }
  virtual VirtualState* as_VirtualState()  { return NULL; }
  virtual EscapedState* as_EscapedState()  { return this; }

#ifndef PRODUCT
  virtual void dump() const;
#endif
};

// Used to iterate _aliases and _alloc_states
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

class IREffect {
#ifdef ASSERT
  const char * _name;
#endif
public:
  IREffect(const char* name) {
#ifdef ASSERT
    _name = name;
#endif  
  }
  virtual void apply() = 0;
};

class BlockState : public ResourceObj {
private:
#ifdef ASSERT
  // Simple control flow graph
  PhaseSimpleCFG* _cfg;
  // Associated basic block
  Block* _block;
#endif
  // Aliases to the same allocation site
  Dict* _aliases; 
  // Related object state for the virtual allocation node
  Dict* _alloc_states;
  // Effect list
  GrowableArray<IREffect*> _effects;

public:
  BlockState();
  BlockState(Block* block);
  BlockState(PhaseSimpleCFG* cfg, Block* block);

  void add_alias(Node* key, Node* value) {
    _aliases->Insert(key, value);
  }
  Node* get_alias(const Node* key) {
    return (Node*)_aliases->operator[]((void*)key);
  }
  void add_alloc_state(VirtualAllocNode* key, AllocState* value) {
    _alloc_states->Insert(key, value);
  }
  void del_alloc_state(VirtualAllocNode* key) {
    _alloc_states->Delete(key);
  }
  AllocState* get_alloc_state(const VirtualAllocNode* key) {
    return (AllocState*)_alloc_states->operator[]((void*)key);
  }
  void add_effect(IREffect* effect) {
    _effects.push(effect);
  }

  Dict* get_aliases() { return _aliases; }
  Dict* get_alloc_states() { return _alloc_states; }

  BlockState* clone();

#ifndef PRODUCT
  void set_block(Block* block) { _block = block; }
  void set_cfg(PhaseSimpleCFG* cfg) { _cfg = cfg; }
  void dump();
#endif
};

class PhasePartialEA : public Phase {
private:
  PhaseIterGVN* _igvn;
  ResourceHashtable<uint, BlockState*> _block_states;
  RegionNode* _merge_point;
  bool _has_allocation;

private:
  void add_block_state(Block* block, BlockState* bstate) {
    bool added = _block_states.put(block->head()->_idx, bstate);
    assert(added == true, "BlockState is already exist");
  }
  BlockState* get_block_state(Block* block) {
    BlockState** bstate =  _block_states.get(block->head()->_idx);
    assert(bstate != NULL, "BlockState is absent");
    return *bstate;
  }
  bool has_block_state(Block* block) {
    BlockState** bstate =  _block_states.get(block->head()->_idx);
    return bstate != NULL;
  }
  BlockState* create_block_state(Block* b) {
    assert(!has_block_state(b), "block already has associated state");
    BlockState* bstate = new (C->comp_arena()) BlockState(b);
    add_block_state(b, bstate);
    return bstate;
  }
  void set_merge_point(RegionNode* merge_point) {
    assert(merge_point != NULL, "invalid merge point");
    _merge_point = merge_point;
  }
  RegionNode* get_merge_point() { return _merge_point; }

private:
  PhiNode* create_phi_for_field(GrowableArray<BlockState*>* pred_bstates, VirtualAllocNode* valloc,
                                Node* field, int field_idx);
  void materialize(VirtualAllocNode* valloc, BlockState* bstate, bool* has_materialization);
  void merge_phi(GrowableArray<BlockState*>* pred_bstates, BlockState* merged_bstate,
                 PhiNode* phi, bool* has_materialization);
  void merge_fields(GrowableArray<BlockState*>* pred_bstates, BlockState* merged_bstate,
                    Node* alias_key_node);
  BlockState* merge_block_states(GrowableArray<BlockState*>* bstates);

public:
  PhasePartialEA(PhaseIterGVN *igvn);

  void do_load(BlockState* bstate, Node* n);
  void do_store(BlockState* bstate, Node* n);
  void do_node(BlockState* bstate, Node* n);
  void do_block(BlockState* bstate, Block* b);
  void do_analysis();

};
#endif // SHARE_OPTO_PARTIAL_ESCAPE_HPP