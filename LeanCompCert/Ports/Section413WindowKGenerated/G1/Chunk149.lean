import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk149

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362657479050518415, 362657481946272807⟩, ⟨(-2587685333295436977), (-2587656145768817563)⟩, true⟩

def state01 : KState := ⟨⟨362553843849502588, 362553846749325634⟩, ⟨(-1043241894579839017), (-1043212646409500843)⟩, true⟩

def words00 : List Nat := [371283837037403577, 371283842680485244, 371283850159885276, 371283857638518466, 371283865273003929, 371283868131801908, 371283870972449255, 371283873812862774, 371283879435160869, 371283884128011873]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362443678487913251, 362443681391798321⟩, ⟨600107914356103024, 600137223112261308⟩, true⟩

def words01 : List Nat := [371283890634796045, 371283897140894378, 371283903669348642, 371283904217543562, 371283905679940012, 371283907142360043, 371283910440237571, 371283910440688829, 371283907761896983, 371283905066269653]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492919163036765, 362492922070964158⟩, ⟨(-134580959957700830), (-134551590869339630)⟩, true⟩

def words02 : List Nat := [371283903194294491, 371283903194795965, 371283904839363494, 371283907904060088, 371283910456494418, 371283910456947051, 371283908491209335, 371283907469268317, 371283909907679190, 371283910511733743]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362554443776077573, 362554446688123137⟩, ⟨(-1053562010011240380), (-1053532579417582436)⟩, true⟩

def words03 : List Nat := [371283910512080987, 371283910378653383, 371283913976083678, 371283916057297378, 371283918778456342, 371283921499426676, 371283924147733930, 371283924391292535, 371283929111967650, 371283933832262246]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362527079994026494, 362527082910098546⟩, ⟨(-644557629428462259), (-644528138658259915)⟩, true⟩

def words04 : List Nat := [371283942038189972, 371283945292674617, 371283948090825675, 371283950888759303, 371283953766349860, 371283954888191090, 371283960482736605, 371283966076712802, 371283970659549712, 371283973543590737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362604664929419369, 362604667849591620⟩, ⟨(-1804713303600455515), (-1804683751511676847)⟩, true⟩

def words05 : List Nat := [371283980898332668, 371283988252336877, 371283998832987249, 371284003463484328, 371284007357292248, 371284011250715679, 371284019611109102, 371284025843846400, 371284033908464369, 371284041972209649]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362564181324529070, 362564184248777629⟩, ⟨(-1199185453590488431), (-1199155840498750961)⟩, true⟩

def words06 : List Nat := [371284050017194134, 371284052118693702, 371284057150820196, 371284062182501623, 371284067853602441, 371284069835953886, 371284071843427401, 371284073850785527, 371284080317700692, 371284085668823134]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468313112634748, 362468316040968590⟩, ⟨236647812147102581, 236677486415742895⟩, true⟩

def words07 : List Nat := [371284093243361446, 371284100817066217, 371284107645331746, 371284108540047557, 371284110676196549, 371284112812296629, 371284117701043441, 371284117701496656, 371284116660418116, 371284115606149882]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362504397028025230, 362504399960411594⟩, ⟨(-303724522400227076), (-303694787403585524)⟩, true⟩

def words08 : List Nat := [371284117220546329, 371284118350936950, 371284123929449189, 371284129507404277, 371284134035785286, 371284134036238939, 371284134703588237, 371284135953907814, 371284140134231476, 371284141486166809]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485641429745930, 362485644366270901⟩, ⟨(-22441491089354142), (-22411694034431838)⟩, true⟩

def words09 : List Nat := [371284142662110996, 371284143838055796, 371284146139296451, 371284147049139812, 371284149309561269, 371284151569850887, 371284153817640506, 371284153818094452, 371284150252769718, 371284150352936162]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk149
