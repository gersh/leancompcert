import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk103

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362417787006417503, 362417788345619952⟩, ⟨684937022878149386, 684946361603498306⟩, true⟩

def state01 : KState := ⟨⟨362464711792637785, 362464713134544255⟩, ⟨201959033178348148, 201968399768975172⟩, true⟩

def words00 : List Nat := [371284284519459443, 371284284519792674, 371284292116922870, 371284300631275458, 371284307235578885, 371284307235880994, 371284301301031626, 371284299999399029, 371284302697739824, 371284302698052401]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362533545985489055, 362533547330156542⟩, ⟨(-508070944426784991), (-508061549355965367)⟩, true⟩

def words01 : List Nat := [371284300798412380, 371284297203521897, 371284299432468939, 371284300729287881, 371284304775308982, 371284308820657896, 371284312729220390, 371284312729530049, 371284316559492568, 371284321329831384]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471819043794646, 362471820391155725⟩, ⟨129646062996128441, 129655485879019133⟩, true⟩

def words02 : List Nat := [371284335500492941, 371284340923070201, 371284345606716879, 371284350289552801, 371284354654466298, 371284354654799435, 371284360739039415, 371284367074168653, 371284371744751404, 371284371745064633]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362613729801374951, 362613731151478236⟩, ⟨(-1336751241810855853), (-1336741790587510109)⟩, true⟩

def words03 : List Nat := [371284378703248334, 371284386874933134, 371284404430639419, 371284409510143312, 371284413581793594, 371284417652754170, 371284431100874383, 371284439943792190, 371284452447987369, 371284464949893524]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362588896101779420, 362588897454618928⟩, ⟨(-1080180459757173203), (-1080170980227145413)⟩, true⟩

def words04 : List Nat := [371284477335946912, 371284477336250126, 371284486563764935, 371284495860345325, 371284507897907396, 371284512320272729, 371284516632362941, 371284520943720127, 371284533108353947, 371284543191240787]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488979924781267, 362488981280359899⟩, ⟨(-45342043759130123), (-45332535865136961)⟩, true⟩

def words05 : List Nat := [371284557875336834, 371284572556721039, 371284583834765171, 371284585059959047, 371284588511656183, 371284591962831722, 371284604754658590, 371284605129972725, 371284605552610676, 371284605975286534]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362565288964747176, 362565290323047396⟩, ⟨(-836127419385052249), (-836117883281705333)⟩, true⟩

def words06 : List Nat := [371284612381938627, 371284615538453033, 371284626028359183, 371284636516361014, 371284645701471395, 371284645701775508, 371284647226335769, 371284649850084893, 371284661790110758, 371284669564848408]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362536763421460325, 362536764782530033⟩, ⟨(-540079615059116188), (-540070050221877490)⟩, true⟩

def words07 : List Nat := [371284677236001463, 371284684905774552, 371284694162501148, 371284701614217285, 371284711748386556, 371284721880720646, 371284732073350250, 371284732073654885, 371284734912193776, 371284739924595164]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362419643740210874, 362419645104001695⟩, ⟨676346098746114654, 676355691842533878⟩, true⟩

def words08 : List Nat := [371284748657679906, 371284748657984984, 371284747733251120, 371284746706994255, 371284746679267909, 371284746679606504, 371284743060240017, 371284742704831406, 371284742349386295, 371284741898211757]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362541313376504797, 362541314743056149⟩, ⟨(-588405236025994993), (-588395614233883623)⟩, true⟩

def words09 : List Nat := [371284738647360328, 371284741660816466, 371284751171220553, 371284751171525676, 371284748355031541, 371284742118004028, 371284736621381552, 371284736621717446, 371284738241339117, 371284743681212684]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk103
