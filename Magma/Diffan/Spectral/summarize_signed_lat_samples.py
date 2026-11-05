#!/usr/bin/env python3
"""Reproducible post-processing of fixed-key RFC Magma signed LAT probes.

The stored five sample batches are DISTINCT deterministic SplitMix64
streams, not a proof of independent uniform random samples.
Use standard errors and z-like ratios only as exploratory diagnostics.
The first two runs (A,B) were examined before nominating the
top_L_to_top_R mask; the other three (C,D,E) are held-out.
No exact full C32 LAT entries are computed by this script.
"""
import json
import math
from pathlib import Path

PATH=Path(__file__).with_name("full32_signed_lat_samples.jsonl")
samples={}
rows={}
for line in PATH.read_text().splitlines():
    kind,value=line.split(" ",1)
    obj=json.loads(value)
    if kind=="FULL32_SIGNED_LAT_PROBE_HEADER":
        s=obj["seed"]
        assert s not in samples
        samples[s]=obj
        rows[s]={}
    elif kind=="FULL32_SIGNED_LAT_ROW":
        rows[s][obj["label"]]=obj
    else:
        raise ValueError(kind)
seeds=[140989193,314159265,975310864,1777777777,4242424242]
assert list(samples)==seeds, list(samples)
labels=list(rows[seeds[0]])
assert len(labels)==14 and all(set(rows[s])==set(labels) for s in seeds)

def aggregate(run_indices,label,stage="c32"):
    used=[seeds[i] for i in run_indices]
    n=sum(samples[s]["samples"] for s in used)
    signed_sum=sum(rows[s][label][stage+"_sum"] for s in used)
    return dict(count=n,signed_sum=signed_sum,estimate=signed_sum/n,
                heuristic_standard_error=1/math.sqrt(n),
                heuristic_z=signed_sum/math.sqrt(n))

first=[0,1]
holdout=[2,3,4]
allruns=list(range(5))
target="top_L_to_top_R"
result={
 "scope":"real RFC full 32-round fixed-key signed Walsh, sampled only",
 "exact_full_LAT":False,
 "seeded_splitmix_sampling_not_provably_independent":True,
 "masks_tested_nontrivial":len(labels)-1,
 "total_samples":sum(samples[s]["samples"] for s in seeds),
 "first_two_runs":aggregate(first,target),
 "holdout_three_runs":aggregate(holdout,target),
 "all_five_runs":aggregate(allruns,target),
 "target_mask":{"a":rows[seeds[0]][target]["a"],"b":rows[seeds[0]][target]["b"]},
 "holdout_other_mask_max_abs_z":max(abs(aggregate(holdout,lab)["heuristic_z"])
                                  for lab in labels if lab not in ("zero",target)),
 "holdout_target_two_sided_gaussian_p_heuristic":math.erfc(
     abs(aggregate(holdout,target)["heuristic_z"])/math.sqrt(2)),
 "all_full_cipher_rows":[
    {"mask":lab,
     "a":rows[seeds[0]][lab]["a"],"b":rows[seeds[0]][lab]["b"],
     "exploratory_z":round(aggregate(first,lab)["heuristic_z"],3),
     "holdout_z":round(aggregate(holdout,lab)["heuristic_z"],3),
     "total_z":round(aggregate(allruns,lab)["heuristic_z"],3)}
    for lab in labels if lab!="zero"
 ]
}
assert result["total_samples"]==1<<30
assert all(samples[s]["gauge_checks"]>=16384 for s in seeds)
print("FULL_32_SIGNED_LAT_SAMPLE_AUDIT",json.dumps(result,sort_keys=True))
