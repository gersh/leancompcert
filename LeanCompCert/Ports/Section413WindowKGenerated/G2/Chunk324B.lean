import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324A

def state06 : KState := ⟨⟨360563276859374260, 360563283239078717⟩, ⟨589960212348258078, 590100240310106576⟩, true⟩

def words05 : List Nat := [360581458511537983, 360581459378604751, 360581460085667327, 360581461290543685, 360581462256268064, 360581463222003499, 360581463636589350, 360581463637022146, 360581463103655631, 360581462544079029]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360546285501952171, 360546291885731379⟩, ⟨1141307462602430814, 1141447622851469606⟩, true⟩

def words06 : List Nat := [360581461984397869, 360581461068451417, 360581459204737352, 360581456863396953, 360581454522130434, 360581451738319758, 360581449683306594, 360581448574279055, 360581447465272725, 360581445800817658]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590823155928392, 360590829543802020⟩, ⟨(-305220254909059429), (-305079961694059171)⟩, true⟩

def words07 : List Nat := [360581444718543711, 360581444051623283, 360581443384615618, 360581442691654471, 360581441732941974, 360581439961485253, 360581438190054389, 360581437053692026, 360581436687382341, 360581436977018545]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546811151532167, 360546817543533343⟩, ⟨1124253439872191806, 1124393867169544112⟩, true⟩

def words08 : List Nat := [360581436977408364, 360581436782902753, 360581435926291951, 360581435215111918, 360581434503861311, 360581433374052831, 360581431731508250, 360581429252545265, 360581426773651870, 360581424926333268]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360542846833755781, 360542853229835189⟩, ⟨1253296112628857686, 1253436672448400026⟩, true⟩

def words09 : List Nat := [360581423861546191, 360581423741220007, 360581423620854008, 360581423026283449, 360581422942137086, 360581422395611124, 360581422246082094, 360581422246515425, 360581421698335502, 360581420512064371]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324B
