import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk858A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk858B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk858A

def state06 : KState := ⟨⟨362488023957341124, 362488135103993662⟩, ⟨(-253422823695104097), (-246979250315830883)⟩, true⟩

def words05 : List Nat := [371285257819125292, 371285257887621162, 371285258090433420, 371285258233759215, 371285258352551313, 371285258472475312, 371285258591392415, 371285258594377287, 371285258565811865, 371285258603017482]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483337519779561, 362483448693042961⟩, ⟨149012967979882964, 155458826308438278⟩, true⟩

def words06 : List Nat := [371285258738682409, 371285258762783884, 371285258786139362, 371285258810529247, 371285258858805976, 371285258862118005, 371285258947713985, 371285259035730928, 371285259087368251, 371285259090461250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495463187451431, 362495574387736134⟩, ⟨(-892273420519682971), (-885825241735730897)⟩, true⟩

def words07 : List Nat := [371285259161767970, 371285259255743367, 371285259470825709, 371285259506162315, 371285259513344010, 371285259521481354, 371285259573499387, 371285259576836359, 371285259698253148, 371285259821746734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484158852810742, 362484270080062073⟩, ⟨78549947854492934, 85000442668101896⟩, true⟩

def words08 : List Nat := [371285259944153503, 371285259947143466, 371285259952650145, 371285259985990101, 371285260050352396, 371285260053338248, 371285259937208459, 371285259821091325, 371285259719658987, 371285259723124923]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469525429008641, 362469636683093242⟩, ⟨1335540394363121337, 1341993194025778917⟩, true⟩

def words09 : List Nat := [371285259792365271, 371285259874305002, 371285259955339481, 371285259958326233, 371285259877908736, 371285259817636897, 371285259755793291, 371285259751786882, 371285259599633403, 371285259421091214]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk858B
