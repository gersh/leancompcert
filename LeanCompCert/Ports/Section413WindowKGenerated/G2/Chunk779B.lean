import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk779A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk779B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk779A

def state06 : KState := ⟨⟨360584021932891594, 360584061440065157⟩, ⟨(-145586625392552386), (-143506410208885396)⟩, true⟩

def words05 : List Nat := [360582219773278254, 360582219982125983, 360582220319421248, 360582220492727974, 360582220525356280, 360582220558070085, 360582220558978104, 360582220644627715, 360582220669156542, 360582220693920176]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593250452447502, 360593289970220004⟩, ⟨(-865213235192244715), (-863132193663224599)⟩, true⟩

def words06 : List Nat := [360582220694916799, 360582220614452766, 360582220479146116, 360582220457136812, 360582220434833688, 360582220344575742, 360582220258490513, 360582220089304562, 360582219919902371, 360582220057128429]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577453160944041, 360577492689221876⟩, ⟨366644450486806659, 368726311168383295⟩, true⟩

def words07 : List Nat := [360582220326038827, 360582220595155522, 360582220734210489, 360582220824858258, 360582220872505666, 360582220920461039, 360582221132312603, 360582221220513800, 360582221221515453, 360582221162050402]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595281167557552, 360595320706337363⟩, ⟨(-1023656802431864868), (-1021574122753410368)⟩, true⟩

def words08 : List Nat := [360582221130742847, 360582221263582541, 360582221560303106, 360582221857229259, 360582222015588040, 360582222016701583, 360582222010903669, 360582221936407043, 360582221921707715, 360582222090820786]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360596324209786191, 360596363759171521⟩, ⟨(-1105026184650428170), (-1102942677796248810)⟩, true⟩

def words09 : List Nat := [360582222177611025, 360582222264520323, 360582222427626137, 360582222717900970, 360582222928134092, 360582223138545809, 360582223266701923, 360582223284963876, 360582223467152532, 360582223649713999]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk779B
