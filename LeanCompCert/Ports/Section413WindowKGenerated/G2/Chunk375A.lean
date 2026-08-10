import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360545475147067500, 360545483763691351⟩, ⟨1351325836773716856, 1351544257878328450⟩, true⟩

def state01 : KState := ⟨⟨360588819950084223, 360588828571468932⟩, ⟨(-274383419563463978), (-274164819903507118)⟩, true⟩

def words00 : List Nat := [360581523983237687, 360581523733108659, 360581523249371474, 360581522410363765, 360581521571320303, 360581520331412945, 360581519718298965, 360581519767170912, 360581519767621244, 360581519653554094]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609261225723194, 360609269851884971⟩, ⟨(-1041325282432470384), (-1041106503561337726)⟩, true⟩

def words01 : List Nat := [360581520558888359, 360581521464327578, 360581522115211146, 360581522115716864, 360581522058394405, 360581521323363477, 360581520588274857, 360581521070229595, 360581521810212743, 360581522550278902]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591193549363583, 360591202180342414⟩, ⟨(-363599623611149441), (-363380663980716661)⟩, true⟩

def words02 : List Nat := [360581522737457078, 360581522737962994, 360581522673309291, 360581522907875799, 360581522908300544, 360581522761396257, 360581522243765372, 360581521184390035, 360581520124974326, 360581520033211224]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566550988344481, 360566559624086105⟩, ⟨561451452798991473, 561670591201281865⟩, true⟩

def words03 : List Nat := [360581520501705935, 360581520970274022, 360581521081560660, 360581521236170080, 360581521236593519, 360581521209125478, 360581521862562955, 360581521944724911, 360581521945179996, 360581521547133556]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588045025821449, 360588053666346494⟩, ⟨(-245691563403171240), (-245472245407497800)⟩, true⟩

def words04 : List Nat := [360581521149001268, 360581520564618964, 360581520336196540, 360581520210519897, 360581520084806996, 360581519357492471, 360581517923233610, 360581517197974153, 360581516472590374, 360581516630171493]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375A
