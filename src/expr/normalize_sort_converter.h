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
 * Implementation of beta reduction node conversion
 */
#ifndef CVC4__EXPR__NORMALIZE_SORT_NODE_CONVERTER_H
#define CVC4__EXPR__NORMALIZE_SORT_NODE_CONVERTER_H

#include "cvc5_private.h"
#include "expr/node_converter.h"
#include <map>

namespace cvc5::internal {

/**
 * NodeConverter implementation that normalizes sorts based on a provided map.
 */
class NormalizeSortNodeConverter : public NodeConverter
{
 public:
  /**
   * Constructor
   * @param normalizedSorts A map that defines how types should be normalized.
   */
  NormalizeSortNodeConverter(const std::map<TypeNode, TypeNode>& normalizedSorts);

  /** Destructor */
  ~NormalizeSortNodeConverter() override {}

 protected:
  /**
   * Overrides the postConvertType method to normalize types.
   * @param tn The type node to normalize.
   * @return The normalized type node if it exists in the map, or tn itself otherwise.
   */
  TypeNode postConvertType(TypeNode tn) override;

 private:
  /** Map storing the normalized sorts */
  std::map<TypeNode, TypeNode> d_normalizedSorts;
};

}  // namespace cvc5::internal

#endif
