#include <string>
#include <tuple>

#include "core/tts.h"
#include "engines/kinduction.h"
#include "frontends/smv_encoder.h"
#include "gtest/gtest.h"
#include "smt/available_solvers.h"
#include "test_encoder_inputs.h"

using namespace pono;
using namespace smt;
using namespace std;

namespace pono_tests {

class TSmvFileUnitTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<
          tuple<SolverEnum, tuple<const string, int, ProverResult>>>
{
};

TEST_P(TSmvFileUnitTests, Encode)
{
  SmtSolver s = create_solver(get<0>(GetParam()));
  s->set_opt("incremental", "true");
  s->set_opt("produce-models", "true");
  TimedTransitionSystem tts(s);
  // PONO_SRC_DIR is a macro set using CMake PROJECT_SRC_DIR
  auto benchmark = get<1>(GetParam());
  string filename = STRFY(PONO_SRC_DIR);
  filename += "/tests/encoders/inputs/smv/";
  filename += get<0>(benchmark);
  SMVEncoder se(filename, tts);

  SafetyProperty prop(tts.solver(), se.propvec()[get<1>(benchmark)]);
  KInduction kind(prop, tts, s);
  ProverResult res = kind.check_until(10);
  std::vector<UnorderedTermMap> cex;
  EXPECT_EQ(res, get<2>(benchmark));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverTSmvFileUnitTests,
                         TSmvFileUnitTests,
                         testing::Combine(testing::ValuesIn({ CVC5 }),
                                          // from test_encoder_inputs.h
                                          testing::ValuesIn(timed_smv_inputs)));

}  // namespace pono_tests
