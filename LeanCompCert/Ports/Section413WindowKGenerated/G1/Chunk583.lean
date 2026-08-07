import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk583

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468546705339901, 362468596426629067⟩, ⟨954983157810520089, 956941267829191235⟩, true⟩

def state01 : KState := ⟨⟨362485761103365312, 362485810842295669⟩, ⟨(-48699722887284209), (-46740584300078253)⟩, true⟩

def words00 : List Nat := [371285010233351468, 371285010215913406, 371285010074203027, 371285010054176854, 371285010033520428, 371285009961345279, 371285009496319036, 371285009317983862, 371285009252421107, 371285009268247890]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490012686784970, 362490062443685675⟩, ⟨(-296609655840307097), (-294649469314406407)⟩, true⟩

def words01 : List Nat := [371285009269748349, 371285009249628008, 371285009500808759, 371285009628851338, 371285009834850654, 371285010041578955, 371285010193142232, 371285010195121182, 371285010152625796, 371285010241746161]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488782416828535, 362488832191260549⟩, ⟨(-224798736422033531), (-222837527377836381)⟩, true⟩

def words02 : List Nat := [371285010624047543, 371285010749643732, 371285010873450754, 371285010997936939, 371285011210076855, 371285011276819485, 371285011483461602, 371285011690913583, 371285011899017024, 371285011966553655]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502191416843815, 362502241209079347⟩, ⟨(-1007078057351918294), (-1005115809735312158)⟩, true⟩

def words03 : List Nat := [371285012104582338, 371285012243575171, 371285012531806881, 371285012533776976, 371285012430316381, 371285012282935889, 371285012279384392, 371285012322473302, 371285012619128576, 371285012916630893]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477991586502935, 362478041396508009⟩, ⟨404837122057680642, 406800406437088070⟩, true⟩

def words04 : List Nat := [371285013212080399, 371285013214052200, 371285013359892184, 371285013543453792, 371285013743550179, 371285013745520593, 371285013553992695, 371285013361704426, 371285013168641509, 371285013125838551]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362448543657996103, 362448593485782947⟩, ⟨2123344396576129891, 2125308718613006781⟩, true⟩

def words05 : List Nat := [371285013025555121, 371285013045611827, 371285013055516272, 371285013057487004, 371285012711296382, 371285012380224556, 371285012048149903, 371285011881812195, 371285011323449935, 371285010701660484]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482697979832191, 362482747825265029⟩, ⟨129924734054396442, 131890086000486764⟩, true⟩

def words06 : List Nat := [371285010079002086, 371285009639904439, 371285009065025770, 371285008784884576, 371285008504171994, 371285008174729762, 371285007681160664, 371285007482562395, 371285007375827721, 371285007377877681]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482439176539189, 362482489039930221⟩, ⟨145028937006903198, 146995337262570664⟩, true⟩

def words07 : List Nat := [371285007340641268, 371285007302746947, 371285007322237373, 371285007324435573, 371285007321794073, 371285007367422050, 371285007368907487, 371285007321933958, 371285006986342415, 371285006945672986]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465657814622980, 362465707695558254⟩, ⟨1124853046754346976, 1126820471335053820⟩, true⟩

def words08 : List Nat := [371285007122163871, 371285007124135546, 371285006952657548, 371285006779036513, 371285006604640128, 371285006519059502, 371285006296294821, 371285006155222162, 371285006013492673, 371285005871124876]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494931989671667, 362494981888458394⟩, ⟨(-584556534603477079), (-582588067587776609)⟩, true⟩

def words09 : List Nat := [371285005541963632, 371285005507527634, 371285005728842963, 371285005779679426, 371285005781209802, 371285005741687698, 371285005868011585, 371285005890967748, 371285006063136822, 371285006236199225]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk583
