import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360528033626500372, 360528039981660209⟩, ⟨1730819359016709021, 1730958590995177865⟩, true⟩

def state01 : KState := ⟨⟨360555762028274889, 360555768387507993⟩, ⟨832249065500218399, 832388429473451497⟩, true⟩

def words00 : List Nat := [360581462981021818, 360581462281777118, 360581461284030016, 360581459547752261, 360581457811511311, 360581455836562083, 360581454575069806, 360581453739013645, 360581452902967342, 360581451461542966]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587258976310556, 360587265339618160⟩, ⟨(-188606697032763609), (-188467200984099547)⟩, true⟩

def words01 : List Nat := [360581450825589458, 360581450982171403, 360581452087043754, 360581452802905959, 360581452803304283, 360581452706392039, 360581452609411588, 360581451996757144, 360581452038708792, 360581452218462610]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624927902830993, 360624934270254562⟩, ⟨(-1410234560002112337), (-1410094930493978495)⟩, true⟩

def words02 : List Nat := [360581452218847735, 360581451829587799, 360581452410881510, 360581453175782173, 360581453690290916, 360581453690723511, 360581453664081949, 360581453154186329, 360581453081648460, 360581454422871072]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549867798129966, 360549874169631228⟩, ⟨1024269196547188612, 1024408958315201750⟩, true⟩

def words03 : List Nat := [360581455447608809, 360581456472359889, 360581456900430467, 360581456900862902, 360581456379730830, 360581455329993423, 360581454280188560, 360581453960918263, 360581453717206583, 360581452744178553]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360629127839301861, 360629134214883655⟩, ⟨(-1547292280554045629), (-1547152386393288263)⟩, true⟩

def words04 : List Nat := [360581451771112854, 360581452200964988, 360581453603959904, 360581455006951044, 360581455496609899, 360581455497042477, 360581455238895539, 360581455440126870, 360581456174790160, 360581457644473089]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk324
