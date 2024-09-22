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
  std::map<Node, uint32_t> subtreeCache;
  std::map<std::string, uint32_t> symbolMap; // {A: 1, B: 2, C: 3}
  std::map<uint32_t, std::vector<std::string>> subtreePattern; // {1: {1}, 2: {1, 2}, 3: {S1, S2}}

  std::string encoding;                 // Concat elements in subtreePattern           
  std::vector<uint32_t> pat;            // Can be obtained from subtreePattern
  std::vector<std::string> symbols;     // List of symbols in this node left to right 
  std::map<std::string, uint32_t> role; // The role of a symbol in the pattern
  uint32_t equivClass;
  NodeInfo() {}

  NodeInfo(Node n,
          const std::map<Node, uint32_t>& sc,
          const std::map<std::string, uint32_t>& sm,
          const std::map<uint32_t, std::vector<std::string>>& sp,
          const std::string& e,
          const std::vector<uint32_t>& p,
          const std::vector<std::string>& s,
          const std::map<std::string, uint32_t>& r,
          uint32_t ec)
      : node(n),
        subtreeCache(sc),
        symbolMap(sm),
        subtreePattern(sp),
        encoding(e),
        pat(p),
        symbols(s),
        role(r),
        equivClass(ec)
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
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__DANESHVAR_H */
