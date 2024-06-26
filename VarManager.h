//
// Created by vedad on 21/08/18.
//

#ifndef TOFERP_VARMENAGER_H
#define TOFERP_VARMENAGER_H

#include <vector>
#include <map>
#include <set>
#include "common.h"

class VarManager
{
private:
    std::map<Var, Var> prop_to_original;
    std::map<Var, Var> prop_to_ferp;
    std::map<Var, std::vector<Lit> *> prop_to_annotation;
    std::vector<std::vector<Lit> *> annotations;
    std::vector<bool> occurring_prop;
public:
    inline VarManager();
    ~VarManager();

    bool is_sat;
    bool has_empty_clause;    
    std::vector<uint32_t> clause_origin;
    std::map<uint32_t, std::vector<uint32_t> * > literal_clause_to_origins;
    std::vector<std::vector<Lit>> clauses;    
    std::vector<bool> is_included;
    std::map<Var, std::vector<uint32_t> *> helper_to_pgs;
    std::map<Var, uint32_t> helper_to_nor;
    int addVariables(const std::vector<Var> &prop, const std::vector<Var> &orig, const std::vector<Lit> &anno);
    void computeNames();
    void writeIsSat(FILE *file);
    void writeExpansions(FILE *file);
    void writeCNF(FILE *file);
    void writeEmptyClause(FILE *file);
    inline void pushClauseOrigin(uint32_t cl);
    inline void addOccurence(Var v);
    inline uint32_t numClauseOrigins() const;
    inline uint32_t getClauseOrigin(uint32_t clause_id) const;
    inline Lit getLitFerp(const Lit l) const;
    bool isHelpVariable(Var v);
    bool isLiteralClause(std::vector<Lit> clause);
};

//////////// INLINE IMPLEMENTATIONS ////////////

VarManager::VarManager()
{
    is_sat = false;
    has_empty_clause = false;
    clause_origin.push_back(0);
}

void VarManager::pushClauseOrigin(uint32_t cl)
{
    clause_origin.push_back(cl);
}

void VarManager::addOccurence(Var v)
{
    if (v >= occurring_prop.size())
        occurring_prop.resize(v + 1, false);
    occurring_prop[v] = true;
}

uint32_t VarManager::numClauseOrigins() const
{
    return (uint32_t)clause_origin.size() - 1;
}

uint32_t VarManager::getClauseOrigin(uint32_t clause_id) const
{
    return clause_origin[clause_id];
}

Lit VarManager::getLitFerp(const Lit l) const
{
    auto it = prop_to_ferp.find(var(l));
    if (it == prop_to_ferp.end())
        return 0;
    return make_lit(it->second, sign(l));
}

#endif // TOFERP_VARMENAGER_H
