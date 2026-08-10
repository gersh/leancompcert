import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk873A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk873B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk873A

def state06 : KState := ⟨⟨360574908080055167, 360574958129552483⟩, ⟨625775662970010955, 628728313770533375⟩, true⟩

def words05 : List Nat := [360582155962593148, 360582155862843177, 360582155762871926, 360582155659941087, 360582155641798430, 360582155590934882, 360582155539935884, 360582155404326785, 360582155192083508, 360582155111166157]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576816211343543, 360576866272671557⟩, ⟨459103975127107143, 462057659518069969⟩, true⟩

def words06 : List Nat := [360582155059556261, 360582155118173887, 360582155119307869, 360582155084321021, 360582155049129869, 360582154959861599, 360582154936098066, 360582154908917870, 360582154881600853, 360582154788861532]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583509250060172, 360583559323261734⟩, ⟨(-125730024001851546), (-122775302161183494)⟩, true⟩

def words07 : List Nat := [360582154746893359, 360582154765837578, 360582154766866355, 360582154728773339, 360582154707717270, 360582154573734430, 360582154439515445, 360582154303337547, 360582154248687988, 360582154266073545]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579279850640303, 360579329935848482⟩, ⟨243744827075182791, 246700598113668587⟩, true⟩

def words08 : List Nat := [360582154267226989, 360582154180181171, 360582153962057215, 360582153875113396, 360582153787828519, 360582153667853354, 360582153509984398, 360582153286706175, 360582153063170777, 360582152920150046]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360549203692786514, 360549253789838650⟩, ⟨2872326649893324276, 2875283456033228634⟩, true⟩

def words09 : List Nat := [360582152966587265, 360582153045566776, 360582153058857549, 360582153060116182, 360582152998983816, 360582152813425067, 360582152627504111, 360582152435307318, 360582152144987513, 360582151769884797]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk873B
