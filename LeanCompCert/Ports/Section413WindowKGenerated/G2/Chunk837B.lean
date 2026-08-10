import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk837A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk837B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk837A

def state06 : KState := ⟨⟨360576463305267404, 360576509165220744⟩, ⟨495952649522206392, 498546786270221854⟩, true⟩

def words05 : List Nat := [360582460445281526, 360582460499870666, 360582460654438374, 360582460922553130, 360582461093240233, 360582461264101871, 360582461363449798, 360582461364651636, 360582461321662829, 360582461251971822]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587258525695299, 360587304396975006⟩, ⟨(-408274497597681649), (-405679412096437441)⟩, true⟩

def words06 : List Nat := [360582461253245098, 360582461363743807, 360582461379184359, 360582461394745656, 360582461395758271, 360582461332115239, 360582461464162936, 360582461596438527, 360582461618935910, 360582461677989959]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610463643080978, 360610509525709442⟩, ⟨(-2352333226649222157), (-2349737190406405479)⟩, true⟩

def words07 : List Nat := [360582461799601278, 360582461921579462, 360582462185564507, 360582462307573725, 360582462309564537, 360582462311680115, 360582462455904076, 360582462671770980, 360582463007510587, 360582463343515313]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582141281188832, 360582187175294774⟩, ⟨20552254701513094, 23149252580771090⟩, true⟩

def words08 : List Nat := [360582463589189570, 360582463727594075, 360582463862079034, 360582463996896914, 360582464052969447, 360582464054171668, 360582463968156185, 360582463773840277, 360582463579300017, 360582463452327604]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567655836775718, 360567701742197613⟩, ⟨1234389666288925091, 1236987612389485445⟩, true⟩

def words09 : List Nat := [360582463589027685, 360582463729252092, 360582463760936065, 360582463762138463, 360582463651618902, 360582463505582848, 360582463359214180, 360582463209398666, 360582463105793319, 360582462930889612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk837B
