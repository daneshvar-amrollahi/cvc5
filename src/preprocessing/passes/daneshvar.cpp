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
 * The strings eager preprocess utility.
 */

#include "preprocessing/passes/daneshvar.h"

#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/sort_to_term.h"
#include "util/string.h"
#include "expr/node_converter.h"
#include "util/statistics_registry.h"
#include "preprocessing/preprocessing_pass_context.h" 

#include <map>
#include <unordered_map>
#include <memory>
#include <tuple>
#include <stack>

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;


namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Daneshvar::Daneshvar(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "daneshvar"),
    d_statistics(statisticsRegistry())
    {};



/*
Recursive DAG traversal
void dfs(
    const Node&n, 
    std::map<std::string, uint32_t>& symbolMap, // key: symbol, value: id (color)
    std::map<uint32_t, std::vector<std::string>>& subtreePattern // key: subtree id, value: pattern (each element is a symbol color or subtree id)
    )
{
    if (n.isVar())
    {
        std::string symbol = n.toString();
        if (symbolMap.find(symbol) == symbolMap.end())
        {
            uint32_t id = symbolMap.size() + 1;
            symbolMap[symbol] = id;
        }
        
        return;
    }


    std::vector<std::string> children;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        if (n[i].isConst())
        {
            continue;
        }

        
        if (n[i].isVar())
        {
            if (symbolMap.find(n[i].toString()) == symbolMap.end())
            {
                dfs(n[i], subtreeCache, symbolMap, subtreePattern);
            }

            children.push_back(std::to_string(symbolMap[n[i].toString()]));
            continue;
        }
        

        if (subtreeCache.find(n[i]) == subtreeCache.end())
        {
            dfs(n[i], subtreeCache, symbolMap, subtreePattern);
        } 
        children.push_back("S" + std::to_string(subtreeCache[n[i]]));
        
    }
    
    uint32_t id = subtreeCache.size() + 1;
    subtreeCache[n] = id;
    // std::cout << "Inserting " << n << " with id " << id << std::endl;
    subtreePattern[id] = children;
}
*/


void Daneshvar::dfs_iterative(
    const Node& root, 
    std::map<uint32_t, std::vector<std::string>>& subtreePattern, 
    std::unordered_map<Node, uint32_t>& subtreeIdMap, 
    std::unordered_map<Node, bool>& visited, 
    std::unordered_map<Node, uint32_t>& parMap, 
    std::unordered_map<std::string, uint32_t>& symbolMap
    )
{

    std::stack<Node> stack;
    stack.push(root);

    // std::cout << "DFSing " << root << std::endl;

    while (!stack.empty())
    {
        Node n = stack.top();

        auto [it, inserted] = visited.emplace(n, false);
        if (inserted)
        {
            for (size_t i = 0; i < n.getNumChildren(); i++)
            {
                if (n[i].isConst())
                {
                    continue; // Skip constants
                }
                parMap[n[i]]++;
                stack.push(n[i]);
            }
            continue;
        }
        else if (!it->second)
        {
            it->second = true;
            if (n.isVar())
            {
                std::string symbol = n.toString();
                uint32_t id = symbolMap.size() + 1;
                symbolMap.emplace(symbol, id);
            }
            else if (!n.isConst())
            {
                std::vector<std::string> children;
                for (size_t i = 0; i < n.getNumChildren(); i++)
                {
                    if (n[i].isConst())
                    {
                        continue; // Skip constants
                    }
                    if (n[i].isVar())
                    {
                        std::string symbol = n[i].toString();
                        children.push_back(std::to_string(symbolMap[symbol]));
                    }
                    else
                    {
                        Assert(subtreeIdMap.find(n[i]) != subtreeIdMap.end());
                        children.push_back("S" + std::to_string(subtreeIdMap[n[i]]));
                    }
                }

                uint32_t id = subtreeIdMap.size() + 1;
                subtreePattern.emplace(id, std::move(children));
                subtreeIdMap.emplace(n, id);
            }
            // Pop the node after processing
            stack.pop();
        }
        else
        {
            // Node has already been processed, pop it
            stack.pop();
        }
    }

    // std::cout << "DFS done" << std::endl;

}




/*
Recursive version
void getPattern(uint32_t treeId, std::map<uint32_t, std::vector<std::string>>& subtreePattern, std::vector<uint32_t>& pat)
{
    std::vector<std::string> pattern = subtreePattern[treeId];
    for (auto& elem : pattern)
    {
        if (elem[0] == 'S') // element is a subtree
        {
            getPattern(std::stoi(elem.substr(1)), subtreePattern, pat);
        }
        else // symbol is a number (color)
        {
            pat.push_back(std::stoi(elem));
        }
    }
}
*/


/*
Recursive version
void collectSymbols(
    const Node& n,
    std::vector<std::string>& symbols)
{
    if (n.isConst())
    {
        // Skip constants
        return;
    }

    if (n.isVar())
    {
        symbols.push_back(n.toString());
        return;
    }

    for (size_t i = 0; i < n.getNumChildren(); ++i)
    {
        collectSymbols(n[i], symbols);
    }
}
*/


void generateEncoding(
    uint32_t rootId,
    const std::map<uint32_t, std::vector<std::string>>& subtreePattern,
    std::string& encoding)
{
    std::stack<uint32_t> stack;
    stack.push(rootId);

    std::unordered_map<uint32_t, bool> visited; // Map to keep track of visited nodes

    std::vector<std::string> encodingList; // Vector to collect encodings in the correct order

    while (!stack.empty())
    {
        uint32_t currentId = stack.top();

        auto [it, inserted] = visited.emplace(currentId, false);
        if (inserted)
        {
            visited[currentId] = false; // Mark as not yet processed

            auto patternIt = subtreePattern.find(currentId);
            if (patternIt != subtreePattern.end())
            {
                const auto& pattern = patternIt->second;
                for (const auto& symbol : pattern)
                {
                    if (!symbol.empty() && symbol[0] == 'S')
                    {
                        uint32_t childId = std::stoi(symbol.substr(1));
                        // If child not yet visited, push onto stack
                        if (visited.find(childId) == visited.end())
                        {
                            stack.push(childId);
                        }
                    }
                }
            }
            else
            {
                if (currentId != 0)
                    std::cerr << "Error: ID " << currentId << " not found in subtreePattern." << std::endl;
                stack.pop();
                continue;
            }
        }
        else if (!it->second)
        {
            // Second time seeing currentId, process it
            // Build the encoding for the current node
            auto patternIt = subtreePattern.find(currentId);
            if (patternIt != subtreePattern.end())
            {
                const auto& pattern = patternIt->second;
                std::string nodeEncoding = std::to_string(currentId) + ":";
                for (const auto& symbol : pattern)
                {
                    nodeEncoding += symbol + ",";
                }
                if (!pattern.empty())
                {
                    nodeEncoding.pop_back(); // Remove the last comma
                }
                nodeEncoding += ";";

                // Collect the encoding
                encodingList.push_back(nodeEncoding);
            }
            else
            {
                // Handle the error: currentId not found in subtreePattern
                if (currentId != 0)
                    std::cerr << "Error: ID " << currentId << " not found in subtreePattern." << std::endl;
            }

            it->second = true; // Mark as processed
            stack.pop();
        }
        else
        {
            // Node has already been processed, pop it
            stack.pop();
        }
    }


    for (auto it = encodingList.rbegin(); it != encodingList.rend(); ++it)
    {
        encoding += *it;
    }
}




void generatePattern(
    uint32_t treeId,
    const std::map<uint32_t, std::vector<std::string>>& subtreePattern,
    std::vector<uint32_t>& pat)
{
    std::stack<uint32_t> stack;

    std::unordered_map<uint32_t, bool> visited;

    // Cache to store patterns of subtrees
    std::unordered_map<uint32_t, std::vector<uint32_t>> patternCache;

    if (treeId != 0)
    {
        stack.push(treeId);
    }

    while (!stack.empty())
    {
        uint32_t currentId = stack.top();

        // Skip nodes with ID 0
        if (currentId == 0)
        {
            stack.pop();
            continue;
        }

        auto it = visited.find(currentId);
        if (it == visited.end())
        {
            // First time seeing currentId
            visited[currentId] = false; // Mark as not yet processed

            // Retrieve the pattern strings for the current node
            auto patternIt = subtreePattern.find(currentId);
            if (patternIt == subtreePattern.end())
            {
                // Handle the error or skip
                stack.pop();
                continue;
            }
            const auto& patternStrs = patternIt->second;

            // Push child subtrees onto the stack
            for (const auto& elem : patternStrs)
            {
                if (!elem.empty() && elem[0] == 'S')
                {
                    uint32_t childId = std::stoul(elem.substr(1));
                    if (childId == 0)
                    {
                        // Skip nodes with ID 0
                        continue;
                    }
                    // If child not yet visited, push onto stack
                    if (visited.find(childId) == visited.end())
                    {
                        stack.push(childId);
                    }
                }
            }

            continue; // Go back to the start of the loop
        }
        else if (!it->second)
        {
            auto patternIt = subtreePattern.find(currentId);
            if (patternIt == subtreePattern.end())
            {
                // Handle the error or skip
                stack.pop();
                continue;
            }
            const auto& patternStrs = patternIt->second;

            std::vector<uint32_t> currentPattern;

            for (const auto& elem : patternStrs)
            {
                if (!elem.empty() && elem[0] == 'S')
                {
                    uint32_t subtreeId = std::stoul(elem.substr(1));
                    if (subtreeId == 0)
                    {
                        continue;
                    }
                    // Append the pattern of the subtree
                    const auto& subtreePatIt = patternCache.find(subtreeId);
                    if (subtreePatIt != patternCache.end())
                    {
                        const auto& subtreePat = subtreePatIt->second;
                        currentPattern.insert(currentPattern.end(), subtreePat.begin(), subtreePat.end());
                    }
                    else
                    {
                        // This should not happen if the DAG is correctly formed
                        std::cerr << "Error: Pattern for subtree ID " << subtreeId << " not found." << std::endl;
                    }
                }
                else
                {
                    // It's a symbol (number)
                    currentPattern.push_back(std::stoul(elem));
                }
            }

            // Cache the pattern for the current node
            patternCache[currentId] = std::move(currentPattern);

            // Mark as processed
            it->second = true;

            // Pop the node
            stack.pop();
        }
        else
        {
            // Node has already been processed, pop it
            stack.pop();
        }
    }

    // After traversal, the pattern for the root is in the cache
    if (patternCache.find(treeId) != patternCache.end())
    {
        pat = std::move(patternCache[treeId]);
    }
    else
    {
        // If the pattern is not found (e.g., treeId was 0), pat remains empty
        pat.clear();
    }
}












void collectSymbols(
    const std::vector<uint32_t>& pattern,
    const std::unordered_map<std::string, uint32_t>& symbolMap,
    std::vector<std::string>& symbols)
{
    std::unordered_map<uint32_t, std::string> reverseSymbolMap;
    for (const auto& [symbol, id] : symbolMap)
    {
        reverseSymbolMap[id] = symbol;
    }

    for (const auto& elem : pattern)
    {
        if (reverseSymbolMap.find(elem) != reverseSymbolMap.end())
        {
            symbols.push_back(reverseSymbolMap.at(elem));
        }
    }
}


void generateRole(
    const std::vector<std::string>& symbols,
    std::map<std::string, int32_t>& role)
{
    for (size_t i = 0; i < symbols.size(); i++)
    {
        if (role.find(symbols[i]) == role.end())
        {
            role[symbols[i]] = i;
        }
    }
}


void normalizePattern(std::vector<uint32_t>& pattern)
{
    std::unordered_map<uint32_t, uint32_t> origToNorm;
    uint32_t nextNormNum = 1;

    for (auto& num : pattern)
    {
        auto it = origToNorm.find(num);
        if (it != origToNorm.end())
        {
            // Number has been seen before; replace with normalized value
            num = it->second;
        }
        else
        {
            // First occurrence; assign next normalized number
            origToNorm[num] = nextNormNum;
            num = nextNormNum;
            ++nextNormNum;
        }
    }
}



std::unique_ptr<NodeInfo> Daneshvar::getNodeInfo(const Node& node, uint32_t id)
{
    std::map<uint32_t, std::vector<std::string>> subtreePattern;
    std::unordered_map<Node, uint32_t> subtreeIdMap; // key: node, value: subtree id
    std::unordered_map<Node, bool> visited;
    std::unordered_map<Node, uint32_t> parMap;
    std::unordered_map<std::string, uint32_t> symbolMap;

    dfs_iterative(node, subtreePattern, subtreeIdMap, visited, parMap, symbolMap);

    // std::cout << "DFS done" << std::endl;

    uint32_t rootId = subtreeIdMap[node];

    std::string encoding;
    generateEncoding(rootId, subtreePattern, encoding);
    // std::cout << "Got encoding" << std::endl;
    std::vector<uint32_t> pattern;    
    generatePattern(rootId, subtreePattern, pattern);
    // std::cout << "Got pattern" << std::endl;
    std::vector<std::string> symbols;    
    collectSymbols(pattern, symbolMap, symbols);
    // std::cout << "Got symbols" << std::endl;
    std::map<std::string, int32_t> role;
    generateRole(symbols, role);
    // std::cout << "Got role" << std::endl;

    normalizePattern(pattern);

    auto ni = std::make_unique<NodeInfo>(
        node, subtreeIdMap, symbolMap, subtreePattern, encoding, pattern, symbols, role, 0, id);

    return ni;

}

void Daneshvar::computeSubtreePattern(const Node& n, std::vector<uint32_t>& rootId)
{
    
    // Fills the above maps and vectors
    // std::cout << "DFSing " << n << std::endl;
    // dfs_iterative(n, d_subtreeCache, symbolMap, subtreePattern);



    /*
    // Encoding
    std::string encoding;
    for (const auto& [id_key, pattern] : subtreePattern) {
        encoding += std::to_string(id_key) + ":";
        for (const auto& symbol : pattern) {
            encoding += symbol + ",";
        }
        if (!pattern.empty()) {
            encoding.pop_back(); // Remove the last comma
        }
        encoding += ";";
    }
    // std::cout << "Got encoding" << std::endl;

    uint32_t treeId = subtreeCache[n];

    // Pattern
    std::vector<uint32_t> pat;
    getPattern(treeId, subtreePattern, pat);
    // getPatternIterative(treeId, subtreePattern, pat);
    // std::cout << "Got pattern" << std::endl;

    // Symbols
    std::vector<std::string> symbols;
    collectSymbols(n, symbols); // n is the root (whole assertion)
    // collectSymbolsIterative(n, symbols);
    // std::cout << "Got symbols" << std::endl;

    // Role
    std::map<std::string, int32_t> role;
    for (size_t i = 0; i < symbols.size(); i++) {
        if (role.find(symbols[i]) == role.end()) {
            role[symbols[i]] = i;
        }
    }
    // std::cout << "Got role" << std::endl;

    // Create NodeInfo using std::make_unique and return the unique_ptr
    auto ni = std::make_unique<NodeInfo>(
        n, subtreeCache, symbolMap, subtreePattern, encoding, pat, symbols, role, 0, id);

    return ni;
    */
}




bool sameClass(const NodeInfo& a, const NodeInfo& b) // Check if two nodes have the same encoding and pattern
{
    return a.encoding == b.encoding && a.pat == b.pat;
}


int numDigits(int n)
{
    if (n == 0)
    {
        return 1;
    }
    int count = 0;
    while (n > 0)
    {
        n = n / 10;
        count++;
    }
    return count;
}




Node rename(const Node& n, 
            std::unordered_map<std::string, Node>& freeVar2node, 
            std::unordered_map<std::string, Node>& boundVar2node, 
            NodeManager* nodeManager,
            PreprocessingPassContext* d_preprocContext)
{
    std::unordered_map<Node, Node> normalized;
    // Stack entries consist of the node and a boolean indicating if it has been visited
    std::stack<std::pair<Node, bool>> stack;
    std::stack<std::unordered_map<std::string, Node>> scopeStack;
    
    // Initialize a global variable counter for bound variables
    static int globalVarCounter = 0;

    // Initialize the stack with the root node, not visited
    stack.push({n, false});
    // Initialize the scope stack with the global scope
    scopeStack.push(boundVar2node);

    while (!stack.empty()) {
        auto [current, visited] = stack.top();
        stack.pop();

        if (visited) {
            // After children are processed
            if (current.isConst()) {
                normalized[current] = current;
                continue;
            }

            if (current.isVar()) {
                if (current.getKind() == cvc5::internal::Kind::BOUND_VARIABLE) {
                    auto& currentScope = scopeStack.top();

                    if (currentScope.find(current.toString()) != currentScope.end()) {
                        normalized[current] = currentScope[current.toString()];
                    } else {
                        int id = globalVarCounter++;
                        std::string new_var_name = "u" + std::string(5 - numDigits(id), '0') + std::to_string(id);
                        Node ret = nodeManager->mkBoundVar(new_var_name, current.getType());
                        currentScope[current.toString()] = ret;
                        normalized[current] = ret;
                    }
                } else {
                    if (freeVar2node.find(current.toString()) != freeVar2node.end()) {
                        normalized[current] = freeVar2node[current.toString()];
                    } else {
                        std::vector<Node> cnodes;
                        int id = freeVar2node.size();
                        std::string new_var_name = "v" + std::string(5 - numDigits(id), '0') + std::to_string(id);
                        cnodes.push_back(nodeManager->mkConst(String(new_var_name, false)));
                        Node gt = nodeManager->mkConst(SortToTerm(current.getType()));
                        cnodes.push_back(gt);
                        Node ret = nodeManager->getSkolemManager()->mkSkolemFunction(SkolemFunId::INPUT_VARIABLE, cnodes);
                        freeVar2node[current.toString()] = ret;
                        normalized[current] = ret;
                        d_preprocContext->addSubstitution(current, ret);
                    }
                }
                continue;
            }

            // Prepare children for node creation
            std::vector<Node> children;
            if (current.getKind() == cvc5::internal::Kind::APPLY_UF) {
                children.push_back(normalized[current.getOperator()]);
            } else if (current.getMetaKind() == metakind::PARAMETERIZED) {
                children.push_back(current.getOperator());
            }

            for (size_t i = 0; i < current.getNumChildren(); i++) {
                children.push_back(normalized[current[i]]);
            }

            // Handle quantifiers (FORALL, EXISTS)
            if (current.getKind() == cvc5::internal::Kind::FORALL || 
                current.getKind() == cvc5::internal::Kind::EXISTS) {
                // Pop the scope after processing
                scopeStack.pop();
            }

            Node ret = nodeManager->mkNode(current.getKind(), children);
            normalized[current] = ret;

        } else {
            // Before processing children
            if (current.isConst() || current.isVar()) {
                // No children to process
                stack.push({current, true});
                continue;
            }

            // Handle quantifiers (FORALL, EXISTS) by creating a new scope
            if (current.getKind() == cvc5::internal::Kind::FORALL || 
                current.getKind() == cvc5::internal::Kind::EXISTS) {
                // Create a new scope
                std::unordered_map<std::string, Node> newScope = scopeStack.top(); // Copy the current scope
                Node bound_vars = current[0];

                for (size_t i = 0; i < bound_vars.getNumChildren(); i++) {
                    // Remove the bound variable from the parent scope
                    newScope.erase(bound_vars[i].toString());
                }

                scopeStack.push(newScope); // Push the new scope onto the stack
            }

            // Mark the current node as visited and push back onto the stack
            stack.push({current, true});

            // Push children onto the stack
            if (current.getKind() == cvc5::internal::Kind::APPLY_UF) {
                stack.push({current.getOperator(), false});
            } else if (current.getMetaKind() == metakind::PARAMETERIZED) {
                // For parameterized nodes, the operator is treated separately
                // No need to push the operator as it's already included in children
            }

            // Push children in reverse order to maintain left-to-right processing
            for (int i = current.getNumChildren() - 1; i >= 0; i--) {
                stack.push({current[i], false});
            }
        }
    }

    return normalized[n];
}






PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    TimerStat::CodeTimer codeTimer(d_statistics.d_passTime);

    // std::cout << "STARTING DANESHVAR PASS" << std::endl; // Note to make sure not timing out on passg



    std::vector<std::unique_ptr<NodeInfo>> nodeInfos;

    /////////////////////////////////////////////////////////////
    // Step 1: Extract NodeInfo for each assertion
    uint32_t nextId = 0; 
    for (const Node& assertion : assertionsToPreprocess->ref())
    {
        // std::cout << "Assertion: " << assertion << std::endl;
        auto ni = getNodeInfo(assertion, nextId++);
        nodeInfos.push_back(std::move(ni));
        // std::cout << std::endl;
    }
    for (const auto&ni: nodeInfos)
    {
        if (ni)
            ni->print();
        std::cout << std::endl;
    }
    // /////////////////////////////////////////////////////////////

    

    /////////////////////////////////////////////////////////////
    // Step 2: Classify assertions into equivalence classes
    // Use NodeInfo pointers in eqClasses
    std::map<uint32_t, std::vector<NodeInfo*>> eqClasses;

    for (auto& niPtr : nodeInfos)
    {
        NodeInfo* current = niPtr.get();
        bool found = false;
        for (auto& [ec, eqClass] : eqClasses)
        {
            if (sameClass(*current, *eqClass[0]))
            {
                eqClass.push_back(current);
                current->equivClass = ec;
                found = true;
                break;
            }
        }
        if (!found)
        {
            eqClasses[current->id] = { current };
            current->equivClass = current->id;
        }
    }

    for (const auto& [ec, eqClass] : eqClasses)
    {
        std::cout << "Equivalence class " << ec << std::endl;
        for (const auto& ni : eqClass)
        {
            std::cout << "Node: " << ni->node << std::endl;
        }
        std::cout << std::endl;
    }

    /////////////////////////////////////////////////////////////




    /////////////////////////////////////////////////////////////
    // Step 3: Sort nodes based on equivalence classes and super-patterns with customized comparison function

    std::map<std::string, std::vector<int32_t>> superpattern; // Cache of superpatterns    

    std::sort(nodeInfos.begin(), nodeInfos.end(),
        [&eqClasses, &superpattern](const std::unique_ptr<NodeInfo>& a, const std::unique_ptr<NodeInfo>& b) {
            if (a->equivClass != b->equivClass) {
                return a->equivClass < b->equivClass;
            }
            // std::cout << "Comparing " << a->node << " and " << b->node << std::endl;
            // std::cout << "Same class" << std::endl;

            size_t minSize = std::min(a->symbols.size(), b->symbols.size());
            for (size_t i = 0; i < minSize; i++) {
                if (a->symbols[i] == b->symbols[i]) {
                    continue;
                }

                // Compute or retrieve superpatterns
                auto getOrComputeSuperpattern = [&](const std::string& symbol) -> std::vector<int32_t> {
                    auto it = superpattern.find(symbol);
                    if (it != superpattern.end()) {
                        return it->second;
                    }

                    std::vector<int32_t> spat;
                    for (const auto& [ec, eqClass] : eqClasses)
                    {
                        std::vector<int32_t> roles;
                        for (const NodeInfo* ni : eqClass)
                        {
                            auto roleIt = ni->role.find(symbol);
                            if (roleIt != ni->role.end())
                            {
                                roles.push_back(roleIt->second);
                            }
                            else {
                                roles.push_back(static_cast<int32_t>(-1));
                            }
                        }
                        
                        std::sort(roles.begin(), roles.end());
                        spat.insert(spat.end(), roles.begin(), roles.end());
                    }

                    superpattern[symbol] = spat;
                    return spat;
                };

                std::vector<int32_t> spat_a = getOrComputeSuperpattern(a->symbols[i]);
                std::vector<int32_t> spat_b = getOrComputeSuperpattern(b->symbols[i]);

                // std::cout << "Comparing symbols " << a->symbols[i] << " and " << b->symbols[i] << std::endl;
                // std::cout << "Superpattern A: ";
                // for (const auto& elem : spat_a)
                // {
                //     std::cout << elem << " ";
                // }
                // std::cout << std::endl;
                // std::cout << "Superpattern B: ";
                // for (const auto& elem : spat_b)
                // {
                //     std::cout << elem << " ";
                // }
                // std::cout << std::endl << std::endl;

                // Compare the superpatterns
                size_t minSpatSize = std::min(spat_a.size(), spat_b.size());
                for (size_t j = 0; j < minSpatSize; j++) {
                    if (spat_a[j] != spat_b[j]) {
                        return spat_a[j] < spat_b[j];
                    }
                }

            }



            return false;
        });

    

    // for (const auto&ni: nodeInfos)
    // {
    //     if (ni)
    //         ni->print();
    //     std::cout << std::endl;
    // }
    /////////////////////////////////////////////////////////////




    //////////////////////////////////////////////////////////////////////
    // Step 4: Normalize the nodes based on the sorted order
    std::unordered_map<std::string, Node> freeVar2node;
    std::unordered_map<std::string, Node> boundVar2node;
    NodeManager* nodeManager = NodeManager::currentNM();
    std::vector<Node> normalizedNodes;
    for (size_t i = 0; i < nodeInfos.size(); i++)
    {
        Node renamed = rename(nodeInfos[i]->node, freeVar2node, boundVar2node, nodeManager, d_preprocContext);
        normalizedNodes.push_back(renamed);
    }
    //////////////////////////////////////////////////////////////////////

    
    for (uint32_t i = 0; i < nodeInfos.size(); i++)
    {
        // std::cout << "Normalized Node " << i << ": " << normalizedNodes[i] << std::endl;
        assertionsToPreprocess->replace(i, normalizedNodes[i]);
    }


    // std::cout << "FINISHED DANESHVAR PASS" << std::endl; // Note to make sure not timing out on passg


  return PreprocessingPassResult::NO_CONFLICT;
  
}


Daneshvar::Statistics::Statistics(StatisticsRegistry& reg)
    : d_passTime(reg.registerTimer("Daneshvar::pass_time"))
{
}




}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal