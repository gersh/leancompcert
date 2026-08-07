import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk302

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507963314038183, 362507975958659712⟩, ⟨(-675573511096476970), (-675315390428252588)⟩, true⟩

def state01 : KState := ⟨⟨362484144783731906, 362484157437088792⟩, ⟨43773398965759799, 44031783486433065⟩, true⟩

def words00 : List Nat := [371285616005196372, 371285616006165295, 371285615667094127, 371285616045629929, 371285616473501146, 371285616474476672, 371285615921090180, 371285615369995529, 371285614959433583, 371285614960540843]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362447802402463316, 362447815064545900⟩, ⟨1142063713795036029, 1142322361964695453⟩, true⟩

def words01 : List Nat := [371285615958694550, 371285617005431156, 371285618028689951, 371285618029659464, 371285617594665017, 371285617491929096, 371285617545280944, 371285617546251415, 371285616524863935, 371285615275067565]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497309849499606, 362497322520268184⟩, ⟨(-354153217235299076), (-353894306530973328)⟩, true⟩

def words02 : List Nat := [371285614024933432, 371285613690423990, 371285613265415859, 371285613600231892, 371285613893877221, 371285613894866421, 371285614116108349, 371285614709965079, 371285615793940779, 371285616182187044]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489487286752983, 362489499966390720⟩, ⟨(-117603659367539963), (-117344480505948003)⟩, true⟩

def words03 : List Nat := [371285616559691107, 371285616937498453, 371285617755334105, 371285618026179333, 371285618627716950, 371285619229576627, 371285619832538561, 371285619833513424, 371285619525972624, 371285619655537708]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362454228860016797, 362454241548286886⟩, ⟨948846971074133090, 949106411022966176⟩, true⟩

def words04 : List Nat := [371285620876335519, 371285620877305910, 371285620642697833, 371285620245427873, 371285619847823371, 371285619567289043, 371285618773173739, 371285618174375598, 371285617575286502, 371285616966833100]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362522235718613333, 362522248415640892⟩, ⟨(-1108724535297070897), (-1108464830390159455)⟩, true⟩

def words05 : List Nat := [371285615930325652, 371285615578362014, 371285615964021866, 371285615965009230, 371285615797281290, 371285615454005906, 371285615726508229, 371285615847376244, 371285617058629174, 371285618270226327]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488336476857644, 362488349182654259⟩, ⟨(-82930178404554309), (-82670208101913493)⟩, true⟩

def words06 : List Nat := [371285619126555473, 371285619127526446, 371285618835301927, 371285619141677708, 371285619777716424, 371285619778688000, 371285619172760380, 371285618448214842, 371285618087787771, 371285618179116157]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362447082029064709, 362447094743612764⟩, ⟨1166242855152335789, 1166503090405167487⟩, true⟩

def words07 : List Nat := [371285619359878778, 371285620540978632, 371285621722884740, 371285621723856141, 371285621453197929, 371285621221254373, 371285621167098923, 371285621168070403, 371285619894942897, 371285618623745036]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469529144021089, 362469541867276019⟩, ⟨486548338839826793, 486808837781472913⟩, true⟩

def words08 : List Nat := [371285617352191784, 371285617062390591, 371285616381795698, 371285616266009411, 371285616149944519, 371285615881058723, 371285614491490404, 371285614000194880, 371285613508428587, 371285613469711856]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480091283974952, 362480104016071139⟩, ⟨166646923220361696, 166907690008099656⟩, true⟩

def words09 : List Nat := [371285612939866291, 371285612329121639, 371285612194349096, 371285612350136578, 371285612799284953, 371285613248801597, 371285613699648040, 371285613700620064, 371285612701303768, 371285612520691869]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk302
