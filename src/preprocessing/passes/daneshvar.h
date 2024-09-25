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
  std::unordered_map<Node, uint32_t> subtreeIdMap;
  std::unordered_map<std::string, uint32_t> symbolMap; // {A: 1, B: 2, C: 3}
  std::map<uint32_t, std::vector<std::string>> subtreePattern; // {1: {1}, 2: {1, 2}, 3: {S1, S2}}

  std::string encoding;                 // Concat elements in subtreePattern           
  std::vector<uint32_t> pat;            // Can be obtained from subtreePattern
  std::vector<std::string> symbols;     // List of symbols in this node left to right 
  std::map<std::string, int32_t> role;  // The role (index of first occurrence) of a symbol in the pattern
  uint32_t equivClass;
  uint32_t id;

  NodeInfo() {}

  NodeInfo(
    const Node& n, 
    const std::unordered_map<Node, uint32_t>& sidMap, 
    const std::unordered_map<std::string, uint32_t>& symMap, 
    const std::map<uint32_t, std::vector<std::string>>& subPattern, 
    const std::string& enc, 
    const std::vector<uint32_t>& p, 
    const std::vector<std::string>& syms, 
    const std::map<std::string, int32_t>& r, 
    uint32_t eqClass, 
    uint32_t i
  ) : node(n), subtreeIdMap(sidMap), symbolMap(symMap), subtreePattern(subPattern), encoding(enc), pat(p), symbols(syms), role(r), equivClass(eqClass), id(i) {}

  void print() const {
    std::cout << "Node : " << node << std::endl;
    std::cout << "Encoding: " << encoding << std::endl;
    std::cout << "Pattern: ";
    for (const auto& elem : pat)
    {
        std::cout << elem << " ";
    }
    std::cout << std::endl;
    std::cout << "Symbols: ";
    for (const auto& symbol : symbols)
    {
        std::cout << symbol << " ";
    }
    std::cout << std::endl;
    std::cout << "Role: ";
    for (const auto& [symbol, idx] : role)
    {
        std::cout << symbol << " : " << idx << " , ";
    }
    std::cout << std::endl;
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

  void computeSubtreePattern(const Node& n, std::vector<uint32_t>& rootId);
  void dfs_iterative(
    const Node& root, 
    std::map<uint32_t, std::vector<std::string>>& subtreePattern, 
    std::unordered_map<Node, uint32_t>& subtreeIdMap, 
    std::unordered_map<Node, bool>& visited, 
    std::unordered_map<Node, uint32_t>& parMap, 
    std::unordered_map<std::string, uint32_t>& symbolMap
  ); 
  std::unique_ptr<NodeInfo> getNodeInfo(const Node& node, uint32_t id);
  Statistics d_statistics;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__DANESHVAR_H */
