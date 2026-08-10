import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk851A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk851B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk851A

def state06 : KState := ⟨⟨360585280876084675, 360585328342757651⟩, ⟨(-250984231535991800), (-248254387991436312)⟩, true⟩

def words05 : List Nat := [360582413818707117, 360582413842056978, 360582413911720162, 360582413912943671, 360582413844867413, 360582413645130541, 360582413445164979, 360582413257307781, 360582413188978088, 360582413224475909]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580508719480419, 360580556197820275⟩, ⟨155415920064447651, 158146757217398039⟩, true⟩

def words06 : List Nat := [360582413225566058, 360582413236693942, 360582413323435430, 360582413410530010, 360582413462617620, 360582413463841437, 360582413418392373, 360582413304321983, 360582413190038486, 360582413034232362]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556551461247958, 360556598951114458⟩, ⟨2196029031688912863, 2198760850623983933⟩, true⟩

def words07 : List Nat := [360582413087818056, 360582413163437708, 360582413164536445, 360582413123327528, 360582413003486925, 360582412848072403, 360582412692261304, 360582412597372624, 360582412364546134, 360582412062767710]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565404132180582, 360565451633615064⟩, ⟨1441907719075601478, 1444640523428926032⟩, true⟩

def words08 : List Nat := [360582411760718774, 360582411564527855, 360582411437321402, 360582411276803533, 360582411116197555, 360582410838761211, 360582410458294425, 360582410124896726, 360582409791151083, 360582409498662945]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564828593355462, 360564876106438761⟩, ⟨1490935290538231703, 1493669087312143277⟩, true⟩

def words09 : List Nat := [360582409300696613, 360582409027928722, 360582408754930854, 360582408619962006, 360582408553830461, 360582408397938108, 360582408241931994, 360582407980551817, 360582407638125372, 360582407433754632]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk851B
