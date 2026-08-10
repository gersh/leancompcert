import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk864A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk864B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk864A

def state06 : KState := ⟨⟨360569449646195006, 360569498630549515⟩, ⟨1096285910283598877, 1099145988632871883⟩, true⟩

def words05 : List Nat := [360582212312117922, 360582212131430691, 360582211950509344, 360582211922652235, 360582211923692680, 360582211910140907, 360582211896474691, 360582211772561458, 360582211544938408, 360582211399328522]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577868195118684, 360577917191172210⟩, ⟨368388871883063368, 371249961789764052⟩, true⟩

def words06 : List Nat := [360582211253298904, 360582211241168100, 360582211184683826, 360582211043250660, 360582210901596229, 360582210726507113, 360582210643138029, 360582210669012922, 360582210670124258, 360582210587284038]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583655036680234, 360583704044493487⟩, ⟨(-132119184908842520), (-129257078082221464)⟩, true⟩

def words07 : List Nat := [360582210538662528, 360582210422192590, 360582210305347604, 360582210273778680, 360582210108408542, 360582209829770164, 360582209550893950, 360582209406020039, 360582209396139786, 360582209414712585]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575022894080273, 360575071913742891⟩, ⟨614382265941950837, 617245397559609265⟩, true⟩

def words08 : List Nat := [360582209415832075, 360582209366354525, 360582209338278369, 360582209381626623, 360582209382685939, 360582209330538792, 360582209178123347, 360582208946794463, 360582208715234647, 360582208523727394]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558517205520190, 360558566236907137⟩, ⟨2042105275705835599, 2044969421419947125⟩, true⟩

def words09 : List Nat := [360582208493267716, 360582208545579735, 360582208546695438, 360582208497276280, 360582208359762190, 360582208188864203, 360582208017600875, 360582207942022222, 360582207773917813, 360582207501894651]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk864B
