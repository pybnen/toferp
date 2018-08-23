//
// Created by vedad on 07/10/17.
//

#include "Reader.h"

#include <assert.h>
#include <algorithm>

int Reader::parseUnsigned(unsigned& ret)
{
  if (*stream < '0' || *stream > '9')
  {
    printf("Error while reading unsigned number\n");
    return 1;
  }
  
  unsigned result = 0;
  while (*stream >= '0' && *stream <= '9')
  {
    assert(result <= result * 10 + (*stream - '0'));
    result = result * 10 + (*stream - '0');
    ++stream;
  }
  ret = result;
  skipWhitespace(stream);
  return 0;
}

int Reader::parseSigned(int& ret)
{
  int sign = 1;
  
  if (*stream == '-')
  {
    sign = -1;
    ++stream;
  }
  
  if (*stream < '0' || *stream > '9')
  {
    printf("Error while reading signed number\n");
    return 2;
  }
  
  int result = 0;
  
  while (*stream >= '0' && *stream <= '9')
  {
    assert(result <= result * 10 + (*stream - '0'));
    result = result * 10 + (*stream - '0');
    ++stream;
  }
  ret = sign * result;
  skipWhitespace(stream);
  return 0;
}

int AnnotationReader::readCNF(VarManager& mngr)
{
  while(*stream == 'c')
  {
    if(!eagerMatch(stream, "c "))
    {
      skipLine(stream);
      continue;
    }
    
    if(*stream == 'x')
    {
      ++stream;
      skipWhitespace(stream);
      Var v; Lit l;
      propositional.clear();
      while (true)
      {
        if (parseUnsigned(v)) return 1;
        if (v == 0) break;
        propositional.push_back(v);
      }
      original.clear();
      while (true)
      {
        if (parseUnsigned(v)) return 2;
        if (v == 0) break;
        original.push_back(v);
      }
      if(propositional.size() != original.size()) return 3;
      annotation.clear();
      while (true)
      {
        if (parseSigned(l)) return 4;
        if (l == 0) break;
        annotation.push_back(l);
      }
      if(mngr.addVariables(propositional, original, annotation)) return 5;
    }
    else if(*stream == 'o')
    {
      ++stream;
      skipWhitespace(stream);
      if(mngr.numClauseOrigins() != 0) return 6;
      uint32_t cl;
      while (true)
      {
        if (parseUnsigned(cl)) return 7;
        if (cl == 0) break;
        mngr.pushClauseOrigin(cl);
      }
    }
    else
      skipLine(stream);
  }
  return 0;
}

int TraceReader::readTrace(VarManager& mngr)
{
  // skip id 0
  trace_clauses.emplace_back();
  trace_id_to_cnf_id.push_back(0);
  antecedents.emplace_back();
  
  while (true)
  {
    if (*stream == EOF) break;
    if (readClause()) return 6;
  }
  
  for(const std::vector<Lit>& clause : trace_clauses)
    for(const Lit l : clause)
      mngr.addOccurence(var(l));
  
  return 0;
}

void TraceReader::writeTrace(VarManager& mngr, FILE* file)
{
  for(uint32_t i = 1; i < trace_clauses.size(); i++)
  {
    fprintf(file, "%d ", i);
    const std::vector<Lit>& clause = trace_clauses[i];
    for(const Lit l : clause)
      fprintf(file, "%d ", mngr.getLitFerp(l));
    fprintf(file, "0 ");
    const std::array<uint32_t, 2>& ante = antecedents[i];
    if(ante[0] == 0)
    {
      fprintf(file, "%d 0\n", mngr.getClauseOrigin(trace_id_to_cnf_id[i]));
    }
    else
    {
      assert(ante[0] != 0 && ante[1] != 0);
      fprintf(file, "%d ", cnf_id_to_trace_id[ante[0]]);
      fprintf(file, "%d 0\n", cnf_id_to_trace_id[ante[1]]);
    }
  }
}

int TraceReader::readClause()
{
  Lit l = 0;
  trace_clauses.push_back(std::vector<Lit>());
  std::vector<Lit>& clause = trace_clauses.back();
  uint32_t index = 0;
  if (parseUnsigned(index)) return 1;
  if (!cnf_id_to_trace_id.insert(std::pair<uint32_t, uint32_t>(index, trace_clauses.size() - 1)).second) return 2;
  trace_id_to_cnf_id.push_back(index);
  
  while (true)
  {
    if (parseSigned(l)) return 3;
    if (l == 0) break;
    clause.push_back(l);
  }
  
  antecedents.push_back(std::array<uint32_t, 2>());
  std::array<uint32_t, 2>& ante = antecedents.back();
  if (parseUnsigned(index)) return 4;
  if (index == 0) return 0;
  ante[0] = index;
  if (parseUnsigned(index)) return 5;
  if (index == 0) return 6;
  ante[1] = index;
  if (parseUnsigned(index)) return 7;
  if (index != 0) return 8;
  
  return 0;
}

/*
void Reader::readComments()
{
  while (*stream == 'c') skipLine(stream);
}

int Reader::readHeader(unsigned& nvars, unsigned& nclauses)
{
  if (!eagerMatch(stream, "p cnf "))
  {
    printf("Error while reading header\n");
    return 3;
  }
  
  skipWhitespace(stream);
  if (parseUnsigned(nvars)) return 3;
  if (parseUnsigned(nclauses)) return 3;
  return 0;
}

int Reader::readPrefix(Formula& f)
{
  while (true)
  {
    readComments();
    if (*stream != 'e' && *stream != 'a') break;
    if (readQuant(f)) return 4;
  }
  
  f.addQuantifier(type_, variables_);
  variables_.clear();
  
  return 0;
}

int Reader::readQuant(Formula& f)
{
  assert(*stream == 'e' || *stream == 'a');
  
  std::vector<bool> appearing_vars;
  
  QuantType type = (*stream == 'e') ? QuantType::EXISTS : QuantType::FORALL;
  
  ++stream;
  skipWhitespace(stream);
  
  if(type_ != type)
  {
    f.addQuantifier(type_, variables_);
    variables_.clear();
  }
  
  type_ = type;
  
  while (true)
  {
    if (*stream == EOF)
    {
      printf("Error when reading non-terminated quantifier\n");
      return 5;
    }
    Var v = 0;
    
    if (parseUnsigned(v)) return 5;
    
    if (v == 0) break;
    
    if (appearing_vars.size() <= v)
      appearing_vars.resize(v + 1, false);
    
    if (!appearing_vars[v])
      variables_.push_back(v);
    appearing_vars[v] = true;
  }
  
  return 0;
}

int Reader::readMatrix(Formula& f)
{
  
  while (true)
  {
    if (*stream == EOF) break;
    if (readClause()) return 6;
    f.addClause(clause_);
  }
  
  return 0;
}

int Reader::readClause()
{
  Lit l = 0;
  clause_.clear();
  while (true)
  {
    if (parseSigned(l)) return 7;
    if (l == 0) break;
    clause_.push_back(l);
  }
  return 0;
}
*/