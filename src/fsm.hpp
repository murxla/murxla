#ifndef __SMTMBT__FSM_HPP_INCLUDED
#define __SMTMBT__FSM_HPP_INCLUDED

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "util.hpp"

namespace smtmbt {
class State;

static RNGenerator s_rng;  // TODO seeded init

class Action
{
 public:
  Action() = delete;
  Action(const std::string& id) : d_id(id) {}
  virtual ~Action() = default;
  virtual void run() {}
  // virtual void untrace(const char* s) {}
  std::string getId() const { return d_id; }

 private:
  std::string d_id;
};

struct ActionTuple
{
  ActionTuple(Action* a, State* next)
      : d_action(a), d_next(next){};

  std::unique_ptr<Action> d_action;
  State* d_next;
};

class State
{
 public:
  void add(Action* action, uint32_t weight, State* next);
  State* run();

 private:
  std::vector<ActionTuple> d_actions;
  std::vector<uint32_t> d_weights;
};

class FSM
{
 public:
  State* new_state();
  void set_init_state(State* init_state);
  void run();

 private:
  std::vector<std::unique_ptr<State>> d_states;
  State* d_cur_state;
};

}  // namespace smtmbt
#endif
