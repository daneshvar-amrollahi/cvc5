/******************************************************************************
 * Top contributors (to current version):
 *   Daneshvar Amrollahi
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * ToDo: write description
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__DANESHVAR_H
#define CVC5__PREPROCESSING__PASSES__DANESHVAR_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {



struct NodeInfo
{
  Node node;
  std::string encoding;
  std::vector<int> pat;
  std::vector<std::string> varNames;
  std::map<std::string, int> role;
  unsigned equivClassId_ass;
  unsigned equivClassId_operands;
  NodeInfo() {}
  NodeInfo(Node n,
           std::string e,
           std::vector<int> p,
           std::vector<std::string> vn,
           std::map<std::string, int> r,
           unsigned ecId_ass,
           unsigned ecId_op)
      : node(n),
        encoding(e),
        pat(p),
        varNames(vn),
        role(r),
        equivClassId_ass(ecId_ass),
        equivClassId_operands(ecId_op)
  {
  }
};



/**
 * Eliminate all extended string functions in the input problem using
 * reductions to bounded string quantifiers.
 */
class Daneshvar : public PreprocessingPass
{
 public:
  Daneshvar(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

private:
  struct Statistics
  {
    
    TimerStat d_passTime;
    Statistics(StatisticsRegistry& reg);
  };

  Statistics d_statistics;
  std::map<int, std::vector<NodeInfo>> d_ec_ass;
  std::map<int, std::vector<NodeInfo>> d_ec_oper;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__DANESHVAR_H */
