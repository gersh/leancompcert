import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk214

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362430227836641611, 362430234004001616⟩, ⟨1155114642256665484, 1155203896784086828⟩, true⟩

def state01 : KState := ⟨⟨362512778172816941, 362512784346151566⟩, ⟨(-611763822034004415), (-611674439619100771)⟩, true⟩

def words00 : List Nat := [371284212972577302, 371284212627366967, 371284211703157300, 371284211925024967, 371284211925541725, 371284211763038604, 371284211228181497, 371284212048821957, 371284214777986563, 371284216113018172]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484199777363566, 362484205956789784⟩, ⟨251556717127425, 341069582998535⟩, true⟩

def words01 : List Nat := [371284217334566792, 371284218556212559, 371284220104445139, 371284220729537299, 371284222027326625, 371284223325255312, 371284224051745418, 371284224052413512, 371284221879640762, 371284221879739504]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362437518275829663, 362437524461202363⟩, ⟨1000499753826710712, 1000589394097643984⟩, true⟩

def words02 : List Nat := [371284223708377737, 371284223709045901, 371284222640234949, 371284221402481794, 371284220164577965, 371284219564174841, 371284217873554421, 371284217090149487, 371284216306598928, 371284215520189654]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487154475445013, 362487160666868587⟩, ⟨(-63316480240419410), (-63226710269140028)⟩, true⟩

def words03 : List Nat := [371284213341974949, 371284212766469794, 371284213783765075, 371284213784445073, 371284213573584254, 371284212984255546, 371284212487336041, 371284212488079797, 371284211659099869, 371284211797400319]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362446396728728469, 362446402926190107⟩, ⟨810525202163853990, 810615101622011784⟩, true⟩

def words04 : List Nat := [371284211797909147, 371284211498469861, 371284208657774924, 371284207449958577, 371284206241933237, 371284205704100994, 371284202274662744, 371284198846181647, 371284195417731120, 371284193840018640]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362408310186673219, 362408316390146792⟩, ⟨1627887062316546495, 1627977090761146981⟩, true⟩

def words05 : List Nat := [371284192078742018, 371284191931659898, 371284191784372037, 371284191640936006, 371284189296821041, 371284187032295082, 371284184767619311, 371284184290800571, 371284180925994670, 371284177391580210]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362420401439993527, 362420407649460435⟩, ⟨1368446356086388356, 1368536513178806762⟩, true⟩

def words06 : List Nat := [371284173857207206, 371284171428505561, 371284168282525696, 371284166425161838, 371284164567763002, 371284162375278913, 371284157297099569, 371284154381593653, 371284151466029398, 371284149452589397]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362424682150980777, 362424688366556703⟩, ⟨1276585128091154749, 1276675416374749601⟩, true⟩

def words07 : List Nat := [371284146484352203, 371284143228736608, 371284139973138888, 371284138710468381, 371284136367463851, 371284134662552235, 371284132957564234, 371284131256814615, 371284126673668808, 371284123907356273]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362425601433236094, 362425607654788645⟩, ⟨1256882352393460844, 1256972769085842428⟩, true⟩

def words08 : List Nat := [371284121140922344, 371284120533387785, 371284117623603509, 371284114151645859, 371284110679761540, 371284107877169072, 371284103991369442, 371284102263697290, 371284100535953788, 371284098709655367]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504142388175093, 362504148615771482⟩, ⟨(-431258826757931251), (-431168280152256673)⟩, true⟩

def words09 : List Nat := [371284095988457217, 371284095424514303, 371284096452093704, 371284096452768563, 371284096121392407, 371284095414495662, 371284094707395471, 371284094566436212, 371284094276412473, 371284095209876303]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk214
