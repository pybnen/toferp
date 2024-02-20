//
// Created by vedad on 07/10/17.
//

#include "Reader.h"
#include <assert.h>
#include <algorithm>
#include <map>

int Reader::parseUnsigned(unsigned &ret)
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

int Reader::parseSigned(int &ret)
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

int AnnotationReader::readCNF(VarManager &mngr)
{
    while (*stream == 'c')
    {
        if (!eagerMatch(stream, "c "))
        {
            skipLine(stream);
            continue;
        }

        if (*stream == 'x')
        {
            ++stream;
            skipWhitespace(stream);
            Var v;
            Lit l;
            propositional.clear();
            while (true)
            {
                if (parseUnsigned(v))
                    return 1;
                if (v == 0)
                    break;
                propositional.push_back(v);
            }
            original.clear();
            while (true)
            {
                if (parseUnsigned(v))
                    return 2;
                if (v == 0)
                    break;
                original.push_back(v);
            }
            if (propositional.size() != original.size())
                return 3;
            annotation.clear();
            while (true)
            {
                if (parseSigned(l))
                    return 4;
                if (l == 0)
                    break;
                annotation.push_back(l);
            }
            if (mngr.addVariables(propositional, original, annotation))
                return 5;
        }
        else if (*stream == 'o')
        {
            ++stream;
            skipWhitespace(stream);
            if (mngr.numClauseOrigins() != 0)
                return 6;
            uint32_t cl;
            while (true)
            {
                if (parseUnsigned(cl))
                    return 7;
                if (cl == 0)
                    break;
                mngr.pushClauseOrigin(cl);
            }
        }
        else if (*stream == 's')
        {
            ++stream;
            skipWhitespace(stream);
            unsigned is_sat;
            parseUnsigned(is_sat);
            mngr.is_sat = (is_sat == 1);
        }
        else
        {
            skipLine(stream);
        }
    }

    std::reverse(mngr.clause_origin.begin(), mngr.clause_origin.end());
    mngr.clause_origin.pop_back();

    if (*stream == 'p')
    {
        skipLine(stream);        
        while (*stream != EOF) {
            Lit literal;
            std::vector<Lit> clause = std::vector<Lit>();
            parseSigned(literal);
            while (literal != 0)
            {
                clause.push_back(literal);
                mngr.addOccurence(var(literal));
                parseSigned(literal);
            }
            if (clause.size() == 0) {
                mngr.has_empty_clause = true;
            }
            mngr.clauses.push_back(clause);

            if (!mngr.isLiteralClause(clause)) {
                std::vector<uint32_t> *o = new std::vector<uint32_t>();
                for (uint32_t j = 0; j < clause.size(); j++)
                {
                    o->push_back(mngr.clause_origin.back());
                    mngr.clause_origin.pop_back();
                }
                mngr.literal_clause_to_origins.insert(
                    std::pair<uint32_t, std::vector<uint32_t>*>((uint32_t)mngr.clauses.size(), o));
            }
        }
    }

    return 0;
}

int TraceReader::readTrace(VarManager &mngr)
{
    // skip id 0
    trace_clauses.emplace_back();
    trace_id_to_cnf_id.push_back(0);
    antecedents.emplace_back();

    while (true)
    {
        if (*stream == EOF)
            break;
        if (readClause())
            return 6;
    }

    for (const std::vector<Lit> &clause : trace_clauses)
        for (const Lit l : clause)
            mngr.addOccurence(var(l));

    return 0;
}

// void TraceReader::writeTraceSAT(VarManager &mngr, FILE *file)
// {
//     /* resolution proof */
//     fprintf(file, "%s", "r\n");
//     for (uint32_t i = 1; i < trace_clauses.size(); i++)
//     {
//         const std::array<uint32_t, 2> &ante = antecedents[i];

//         if (ante[0] != 0)
//         {
//             assert(ante[0] != 0 && ante[1] != 0);
        
//             fprintf(file, "%d ", trace_id_to_cnf_id[i]);

//             const std::vector<Lit> &clause = trace_clauses[i];
//             for (const Lit l : clause)
//             {
//                 fprintf(file, "%d ", mngr.getLitFerp(l));
//             }
//             fprintf(file, "0 ");
            
//             fprintf(file, "%d ", ante[0]);
//             fprintf(file, "%d 0\n", ante[1]);        
//         }
//     }
// }

void TraceReader::writeTraceSAT(VarManager &mngr, FILE *file)
{
    bool resolution_proof = false;
    for (uint32_t i = 1; i < trace_clauses.size(); i++)
    {        
        const std::array<uint32_t, 2> &ante = antecedents[i];
        if (ante[0] == 0)
        {
            fprintf(file, "%d ", i);
            const std::vector<Lit> &clause = mngr.clauses[trace_id_to_cnf_id[i] - 1];
            // const std::vector<Lit> &clause = trace_clauses[i];
            for (const Lit l : clause) {
                fprintf(file, "%d ", mngr.getLitFerp(l));
            }
            fprintf(file, "0 ");

            if (mngr.literal_clause_to_origins.find(trace_id_to_cnf_id[i]) != mngr.literal_clause_to_origins.end()) {
                auto orig = mngr.literal_clause_to_origins.at(trace_id_to_cnf_id[i]);
                for (auto o : *orig) {
                    fprintf(file, "%d ", o);
                }
            }
            fprintf(file, "%s", "0\n");
        }
        else
        {     
            if (!resolution_proof) {
                fprintf(file, "%s", "r\n");
                resolution_proof = true;
            }
            assert(ante[0] != 0 && ante[1] != 0);

            fprintf(file, "%d ", i);
            const std::vector<Lit> &clause = trace_clauses[i];
            for (const Lit l : clause) {
                fprintf(file, "%d ", mngr.getLitFerp(l));
            }
            fprintf(file, "0 ");
            fprintf(file, "%d ", cnf_id_to_trace_id[ante[0]]);
            fprintf(file, "%d 0\n", cnf_id_to_trace_id[ante[1]]);
        }
    }
}

void TraceReader::writeTrace(VarManager &mngr, FILE *file)
{
    for (uint32_t i = 1; i < trace_clauses.size(); i++)
    {
        fprintf(file, "%d ", i);
        const std::vector<Lit> &clause = trace_clauses[i];
        for (const Lit l : clause) {
            fprintf(file, "%d ", mngr.getLitFerp(l));
        }
        fprintf(file, "0 ");
        const std::array<uint32_t, 2> &ante = antecedents[i];
        if (ante[0] == 0)
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
    std::vector<Lit> &clause = trace_clauses.back();
    uint32_t index = 0;
    if (parseUnsigned(index))
    {
        return 1;
    }

    if (!cnf_id_to_trace_id.insert(std::pair<uint32_t, uint32_t>(index, trace_clauses.size() - 1)).second)
    {
        return 2;
    }

    trace_id_to_cnf_id.push_back(index);

    while (true)
    {
        if (parseSigned(l))
            return 3;
        if (l == 0)
            break;
        clause.push_back(l);
    }

    antecedents.push_back(std::array<uint32_t, 2>());
    std::array<uint32_t, 2> &ante = antecedents.back();
    if (parseUnsigned(index))
        return 4;
    if (index == 0)
        return 0;
    ante[0] = index;
    if (parseUnsigned(index))
        return 5;
    if (index == 0)
        return 6;
    ante[1] = index;
    if (parseUnsigned(index))
        return 7;
    if (index != 0)
        return 8;

    return 0;
}
