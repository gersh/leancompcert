import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk924A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590334338889778, 360590390574235077⟩, ⟨(-780379411998147927), (-776870618936435851)⟩, true⟩

def state01 : KState := ⟨⟨360585538374911780, 360585594622821667⟩, ⟨(-337190166837942359), (-333680212742119243)⟩, true⟩

def words00 : List Nat := [360581983183620209, 360581983314519701, 360581983387034183, 360581983459688151, 360581983502837025, 360581983604828875, 360581983674215806, 360581983743838208, 360581983754510700, 360581983794968467]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360610635525041009, 360610691785570829⟩, ⟨(-2656590916323488517), (-2653079795958867659)⟩, true⟩

def words01 : List Nat := [360581983819543935, 360581983844521264, 360581983986065285, 360581984188827488, 360581984282876256, 360581984377029524, 360581984506140894, 360581984701272858, 360581985012968936, 360581985324961673]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604575922778429, 360604632196073220⟩, ⟨(-2096606186553355091), (-2093093886389450603)⟩, true⟩

def words02 : List Nat := [360581985541385107, 360581985739890408, 360581986001386384, 360581986263268483, 360581986494724305, 360581986659228093, 360581986764813966, 360581986870566768, 360581987015619015, 360581987262161552]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579072090736482, 360579128376606390⟩, ⟨260901422003548514, 264414884550529422⟩, true⟩

def words03 : List Nat := [360581987625159052, 360581987988405407, 360581988263738887, 360581988446003305, 360581988535830299, 360581988625988028, 360581988771062901, 360581988799646835, 360581988800849285, 360581988771289975]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596670215316501, 360596726513831487⟩, ⟨(-1365922967150891741), (-1362408335631606441)⟩, true⟩

def words04 : List Nat := [360581988795917096, 360581988945295139, 360581989123358912, 360581989301679156, 360581989380400150, 360581989419516458, 360581989556753663, 360581989694396036, 360581989807895036, 360581989968681823]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk924A
