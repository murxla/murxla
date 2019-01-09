#ifndef __SMTMBT__FSM_HPP_INCLUDED
#define __SMTMBT__FSM_HPP_INCLUDED

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "solver_manager.hpp"
#include "util.hpp"

namespace smtmbt {
class State;

static RNGenerator s_rng;  // TODO seeded init

struct ActionTuple
{
  ActionTuple(Action* a, State* next)
      : d_action(a), d_next(next){};

  Action* d_action;
  State* d_next;
};

class State
{
  friend class FSM;

 public:
  State() : d_id("") {}
  State(std::string& id) : d_id(id) {}
  const std::string& get_id() { return d_id; }
  State* run();
  void add_action(Action* action, uint32_t weight, State* next = nullptr);

 private:
  std::string d_id;
  std::vector<ActionTuple> d_actions;
  std::vector<uint32_t> d_weights;
};

class FSM
{
 public:
  State* new_state(std::string id = "");
  void set_init_state(State* init_state);
  void check_states();
  void run();

 private:
  std::vector<std::unique_ptr<State>> d_states;
  State* d_cur_state;
};

}  // namespace smtmbt
#endif
