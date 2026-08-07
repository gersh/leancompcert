import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk379

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589824297290780, 360589833106299384⟩, ⟨(-308408083288463498), (-308182409211351904)⟩, true⟩

def state01 : KState := ⟨⟨360672990384137574, 360672999197972895⟩, ⟨(-3460884758328590449), (-3460658901295410475)⟩, true⟩

def words00 : List Nat := [360581702597179553, 360581703683147778, 360581705141900728, 360581706600675015, 360581707448136021, 360581708190922555, 360581709628541109, 360581711066241980, 360581713022256439, 360581715430694390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360637585210305920, 360637594029011617⟩, ⟨(-2118380743414949227), (-2118154701720996843)⟩, true⟩

def words01 : List Nat := [360581717489922185, 360581719549106120, 360581722019516153, 360581724918652167, 360581727641483438, 360581730364254605, 360581732550594542, 360581734044840590, 360581735518362110, 360581736991968264]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604624450779653, 360604633274304079⟩, ⟨(-868374169921088653), (-868147945477469691)⟩, true⟩

def words02 : List Nat := [360581738672425449, 360581739879879771, 360581740738711854, 360581741597555707, 360581742017728353, 360581743009599711, 360581743847093333, 360581744684642493, 360581745112807610, 360581745716752803]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628580318598895, 360628589146956961⟩, ⟨(-1777159341406021975), (-1776932933598368061)⟩, true⟩

def words03 : List Nat := [360581746842408131, 360581747968154453, 360581749073448146, 360581749983717402, 360581750314484819, 360581750645270088, 360581751433185486, 360581752567979127, 360581753802886398, 360581755037850761]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602685620623028, 360602694453855387⟩, ⟨(-794816046761830941), (-794589454000502521)⟩, true⟩

def words04 : List Nat := [360581755924576455, 360581756356897167, 360581757084268937, 360581757811758537, 360581758363851930, 360581758364363783, 360581758225713705, 360581757525016807, 360581756824258742, 360581757207037109]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596780591040435, 360596789429086716⟩, ⟨(-570532477342935973), (-570305701868145293)⟩, true⟩

def words05 : List Nat := [360581758452074501, 360581759697144317, 360581760594768791, 360581761511436297, 360581762253041112, 360581762994742325, 360581764428988011, 360581765172931633, 360581765569179455, 360581765965482803]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360629163881541282, 360629172724427725⟩, ⟨(-1800090325194099765), (-1799863365963364981)⟩, true⟩

def words06 : List Nat := [360581765965908360, 360581765954155043, 360581766891080458, 360581767828054560, 360581768172293550, 360581768172805971, 360581768761135797, 360581769401840284, 360581770475649960, 360581771724560370]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602250497034361, 360602259344801252⟩, ⟨(-778130848739850154), (-777903704174371828)⟩, true⟩

def words07 : List Nat := [360581772626651546, 360581773528750421, 360581774293622869, 360581775404405087, 360581776003420436, 360581776602479673, 360581776854083932, 360581776874428390, 360581777414138894, 360581777953995998]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617058406755462, 360617067259353587⟩, ⟨(-1340649377486291873), (-1340422049406443575)⟩, true⟩

def words08 : List Nat := [360581778788992279, 360581779642381845, 360581779970929101, 360581780299512067, 360581780334394097, 360581780806630314, 360581781970360218, 360581783134126973, 360581783709220030, 360581784638485318]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360677778409329996, 360677787266766900⟩, ⟨(-3647626327237879130), (-3647398815309118142)⟩, true⟩

def words09 : List Nat := [360581786259147264, 360581787879873972, 360581790191891002, 360581792468402703, 360581794058155801, 360581795647873792, 360581797928795523, 360581800560501668, 360581803086884354, 360581805613249648]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk379
