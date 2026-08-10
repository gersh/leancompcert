import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk797A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk797B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk797A

def state06 : KState := ⟨⟨360575341616808391, 360575383043262140⟩, ⟨541534972519827228, 543766548918013842⟩, true⟩

def words05 : List Nat := [360582203252885897, 360582202942199649, 360582202631186575, 360582202450408756, 360582202112681857, 360582201641053755, 360582201169219092, 360582200854743049, 360582200662023217, 360582200577727010]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560327481397048, 360560368918709171⟩, ⟨1739015256296205348, 1741247698811493908⟩, true⟩

def words06 : List Nat := [360582200493275531, 360582200290393109, 360582200019046813, 360582199820089095, 360582199620846208, 360582199292415206, 360582198807054391, 360582198242888020, 360582197678511776, 360582197271458469]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540325798234288, 360540367246298050⟩, ⟨3334711829636991803, 3336945129864842067⟩, true⟩

def words07 : List Nat := [360582196998742953, 360582196853576107, 360582196708260098, 360582196484417672, 360582196103591295, 360582195681973098, 360582195260018946, 360582194995189320, 360582194607328643, 360582194084225662]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557917837637726, 360557959296468190⟩, ⟨1931048540477176228, 1933282699725283686⟩, true⟩

def words08 : List Nat := [360582193560886234, 360582192968818814, 360582192454946403, 360582191965645898, 360582191476280191, 360582190856718460, 360582190291213924, 360582189799243353, 360582189306950147, 360582188933010681]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557326581419776, 360557368051138378⟩, ⟨1978196433304336701, 1980431461366803739⟩, true⟩

def words09 : List Nat := [360582188630363467, 360582188249256532, 360582187867956812, 360582187483060861, 360582187225945943, 360582186929858709, 360582186633654847, 360582186241903091, 360582185797668458, 360582185487997612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk797B
