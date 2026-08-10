import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk522A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593257984790308, 360593275138948151⟩, ⟨(-587779657161329875), (-587174619914244615)⟩, true⟩

def state01 : KState := ⟨⟨360600796124952704, 360600813285918904⟩, ⟨(-981317228375664171), (-980711835698995887)⟩, true⟩

def words00 : List Nat := [360582027380934286, 360582027740737768, 360582027916646611, 360582028092628207, 360582028121832311, 360582028486470958, 360582028819165017, 360582029151986369, 360582029300574577, 360582029661094653]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599786433147166, 360599803600943935⟩, ⟨(-928634806213396670), (-928029056879039254)⟩, true⟩

def words01 : List Nat := [360582030317686777, 360582030974467548, 360582031620549481, 360582031900861923, 360582031901528738, 360582031847066246, 360582031792471320, 360582031733861602, 360582032074773100, 360582032415848303]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574522213245532, 360574539387924738⟩, ⟨390645194128123788, 391251302898597034⟩, true⟩

def words02 : List Nat := [360582032511930322, 360582032512653505, 360582032338599937, 360582032435115071, 360582032435720917, 360582032436327059, 360582032071110235, 360582031420825402, 360582030770422614, 360582030318479948]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559037969674214, 360559055151163337⟩, ⟨1199561939811975887, 1200168404298636857⟩, true⟩

def words03 : List Nat := [360582030193668625, 360582030212413200, 360582030213058408, 360582029998788203, 360582029999393931, 360582029837471185, 360582029878500469, 360582029879223836, 360582029717391339, 360582029278351290]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583149868079788, 360583167056409033⟩, ⟨(-60287954514879807), (-59681132667767281)⟩, true⟩

def words04 : List Nat := [360582028839175920, 360582028241838110, 360582027829086241, 360582027685252499, 360582027541374596, 360582027077374733, 360582026343415869, 360582025718364773, 360582025093111654, 360582024855634546]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk522A
