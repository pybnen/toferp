#include <zlib.h>
#include <assert.h>
#include <sys/resource.h>

#include "Reader.h"

// taken from qrpcheck
static inline double read_cpu_time()
{
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  return u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec +
         u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
}


int main(int argc, const char *argv[])
{
    if (argc != 4)
    {
        printf("usage: %s <CNF> <TRACE> <FERP>\n", argv[0]);
        return -1;
    }

    double start_time = read_cpu_time();

    const char *cnf_name = argv[1];
    const char *trace_name = argv[2];
    const char *ferp_name = argv[3];

    gzFile cnf_file = gzopen(cnf_name, "rb");

    if (cnf_file == Z_NULL)
    {
        printf("Could not open file: %s", cnf_name);
        return -2;
    }

    gzFile trace_file = gzopen(trace_name, "rb");

    if (trace_file == Z_NULL)
    {
        printf("Could not open file: %s", trace_name);
        return -3;
    }

    FILE *ferp_file = fopen(ferp_name, "wb");

    if (ferp_file == nullptr)
    {
        printf("Could not open file: %s", ferp_name);
        return -4;
    }

    VarManager vmngr;

    AnnotationReader cnf_reader(cnf_file);

    int res = cnf_reader.readCNF(vmngr);
    gzclose(cnf_file);
    if (res != 0)
    {
        printf("Something went wrong while reading CNF, code %d", res);
        return res;
    }

    TraceReader trace_reader(trace_file);

    res = trace_reader.readTrace(vmngr);
    gzclose(trace_file);
    if (res != 0)
    {
        printf("Something went wrong while reading TRACE, code %d", res);
        return res;
    }

    vmngr.computeNames();
    if (vmngr.is_sat) {
        vmngr.writeIsSat(ferp_file);
        if (vmngr.has_empty_clause) {
            vmngr.writeEmptyClause(ferp_file);
            assert(trace_reader.trace_clauses.size() == 1);
            trace_reader.writeTrace(vmngr, ferp_file);
        } else {
            vmngr.writeExpansions(ferp_file);
            trace_reader.writeTraceSAT(vmngr, ferp_file);
        }
    } else {
        vmngr.writeExpansions(ferp_file);
        trace_reader.writeTrace(vmngr, ferp_file);
    }

    fclose(ferp_file);

    double cpu_time = read_cpu_time() - start_time;
    printf("ToFerp was running for %.6f s\n", cpu_time);
    return 0;
}