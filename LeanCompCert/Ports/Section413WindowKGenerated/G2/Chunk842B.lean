import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk842A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk842B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk842A

def state06 : KState := ⟨⟨360607176199949400, 360607222630381273⟩, ⟨(-2091192876163716481), (-2088550813398808269)⟩, true⟩

def words05 : List Nat := [360582433767943445, 360582434064808999, 360582434403432364, 360582434637627948, 360582434738835940, 360582434840135126, 360582435056197447, 360582435355390431, 360582435650561373, 360582435945991119]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608781597635659, 360608828039576590⟩, ⟨(-2226568442023688257), (-2223925409447241307)⟩, true⟩

def words06 : List Nat := [360582436170755538, 360582436254994049, 360582436479694732, 360582436704745306, 360582436863206877, 360582437079526797, 360582437224569444, 360582437369729530, 360582437562232689, 360582437876775066]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577778404897101, 360577824858247885⟩, ⟨386241670566161527, 388885664707486003⟩, true⟩

def words07 : List Nat := [360582438170246620, 360582438463937854, 360582438649321019, 360582438760523930, 360582438834938086, 360582438909682554, 360582439085621694, 360582439121183573, 360582439122266626, 360582439068792588]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607402829240903, 360607449294003840⟩, ⟨(-2110615109021148022), (-2107970153006413898)⟩, true⟩

def words08 : List Nat := [360582439075870296, 360582439245844281, 360582439522328900, 360582439799041373, 360582439955979776, 360582440135601596, 360582440311348983, 360582440487430469, 360582440748997398, 360582441046942987]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599509053822702, 360599555530109205⟩, ⟨(-1445235616812527343), (-1442589689420560541)⟩, true⟩

def words09 : List Nat := [360582441274287656, 360582441501764762, 360582441706560600, 360582442026629953, 360582442271358396, 360582442516277549, 360582442690654906, 360582442754294467, 360582442958271287, 360582443162647128]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk842B
