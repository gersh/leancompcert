import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk291A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566595939503666, 360566601019314644⟩, ⟨479900761200554336, 480000736009994868⟩, true⟩

def state01 : KState := ⟨⟨360580635797470256, 360580640880907047⟩, ⟨71197236515555537, 71297316853382097⟩, true⟩

def words00 : List Nat := [360583095934231683, 360583095934616491, 360583095372223096, 360583094157817725, 360583092943432143, 360583091430260777, 360583091016393243, 360583090940648192, 360583090864865899, 360583090118861475]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584956357539383, 360584961444614044⟩, ⟨(-54698713123458394), (-54598526868930396)⟩, true⟩

def words01 : List Nat := [360583090696215800, 360583091357771471, 360583091991240965, 360583091991625977, 360583091452306921, 360583089920444138, 360583088388614824, 360583087026424131, 360583086494795255, 360583086559587125]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360552458448896317, 360552463539635946⟩, ⟨891475608221172201, 891575901218125383⟩, true⟩

def words02 : List Nat := [360583086559931167, 360583085782389508, 360583083832407757, 360583083058251519, 360583082284043301, 360583081160067132, 360583078863873024, 360583075628447884, 360583072393168841, 360583070333361251]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554280673212272, 360554285767578937⟩, ⟨838546943000289712, 838647341671278398⟩, true⟩

def words03 : List Nat := [360583069407465606, 360583069532295571, 360583069532643964, 360583068892847590, 360583068294735494, 360583067398858085, 360583066781322277, 360583066781708632, 360583066691084911, 360583065703806504]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360647338154692833, 360647343252704773⟩, ⟨(-1873860479015708644), (-1873759974103937670)⟩, true⟩

def words04 : List Nat := [360583064716514373, 360583063316069762, 360583062559911571, 360583062621432781, 360583062621788542, 360583061617490268, 360583061444947124, 360583061945860760, 360583063321801657, 360583065527271549]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk291A
