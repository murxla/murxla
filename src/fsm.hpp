#ifndef __SMTMBT__FSM_HPP_INCLUDED
#define __SMTMBT__FSM_HPP_INCLUDED

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "solver_manager.hpp"
#include "util.hpp"

namespace smtmbt {
class State;

class Action
{
 public:
  Action() = delete;
  Action(SolverManager& smgr, const std::string& id)
      : d_rng(smgr.get_rng()),
        d_solver(smgr.get_solver()),
        d_smgr(smgr),
        d_id(id)
  {
  }
  virtual ~Action()  = default;
  virtual bool run() = 0;
  // virtual void untrace(const char* s) {}
  const std::string& get_id() const { return d_id; }

 protected:
  RNGenerator& d_rng;
  Solver& d_solver;
  SolverManager& d_smgr;

 private:
  std::string d_id;
};

struct ActionTuple
{
  ActionTuple(Action* a, State* next) : d_action(a), d_next(next){};

  Action* d_action;
  State* d_next;
};

class State
{
  friend class FSM;

 public:
  State() : d_id(""), d_is_final(false) {}
  State(std::string& id, std::function<bool(void)> fun, bool is_final)
      : d_id(id), d_is_final(is_final), f_precond(fun)
  {
  }

  const std::string& get_id() { return d_id; }
  bool is_final() { return d_is_final; }
  State* run(RNGenerator& rng);
  void add_action(Action* action, uint32_t weight, State* next = nullptr);
  void set_precondition();

 private:
  std::string d_id;
  bool d_is_final;
  std::function<bool(void)> f_precond;
  std::vector<ActionTuple> d_actions;
  std::vector<uint32_t> d_weights;
};

class FSM
{
 public:
  class TraceStream
  {
   public:
    TraceStream(SolverManager& smgr);
    ~TraceStream();
    TraceStream(const TraceStream& astream) = default;

    std::ostream& stream();

   private:
    void flush();
    SolverManager& d_smgr;
  };

  FSM(RNGenerator& rng, Solver* solver, std::ostream& trace);

  FSM() = delete;

  State* new_state(std::string id                = "",
                   std::function<bool(void)> fun = nullptr,
                   bool is_final                 = false);

  template <class T>
  T* new_action();

  void set_init_state(State* init_state);
  void check_states();
  void run();
  void configure();

 private:
  SolverManager d_smgr;
  RNGenerator& d_rng;
  std::vector<std::unique_ptr<State>> d_states;
  std::unordered_map<std::string, std::unique_ptr<Action>> d_actions;
  State* d_init_state = nullptr;
  State* d_cur_state  = nullptr;
};

template <class T>
T*
FSM::new_action()
{
  static_assert(std::is_base_of<Action, T>::value,
                "expected class (derived from) Action");
  T* action             = new T(d_smgr);
  const std::string& id = action->get_id();
  if (d_actions.find(id) == d_actions.end())
  {
    d_actions[id].reset(action);
  }
  else
  {
    delete action;
  }
  return static_cast<T*>(d_actions[id].get());
}

}  // namespace smtmbt
#endif
