#ifndef __SMTMBT__FSM_HPP_INCLUDED
#define __SMTMBT__FSM_HPP_INCLUDED

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace smtmbt {
class State;

class Action
{
 public:
  Action() = delete;
  Action(const std::string& id) : d_id(id) {}
  virtual void run() {}
  // virtual void untrace(const char* s) {}
  std::string getId() const { return d_id; }

 private:
  std::string d_id;
};

struct ActionTuple
{
  ActionTuple(Action* a, uint32_t weight, State* next)
      : d_action(a), d_weight(weight), d_next(next){};

  std::unique_ptr<Action> d_action;
  uint32_t d_weight;
  State* d_next;
};

class State
{
 public:
  void add(Action* action, uint32_t weight, State* next);

 private:
  State* pick();
  std::vector<ActionTuple> d_actions;
};

class FSM
{
 public:
  State* new_state();
  void set_init_state(State* init_state);
  void set_final_state(State* final_state);
  void run();

 private:
  std::vector<std::unique_ptr<State>> d_states;
  State* d_cur_state;
  State* d_final_state;
};

}  // namespace smtmbt
#endif
