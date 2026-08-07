import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk253

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362425884981588224, 362425893725065645⟩, ⟨1513747750378123038, 1513897308593093118⟩, true⟩

def state01 : KState := ⟨⟨362476148314631036, 362476157065247777⟩, ⟨241953242040065924, 242102980916859902⟩, true⟩

def words00 : List Nat := [371285729198854240, 371285728394777740, 371285726814161540, 371285726793834741, 371285726773265388, 371285726348678168, 371285723844895321, 371285722901039844, 371285722571371088, 371285722572198266]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362438055398302475, 362438064156218245⟩, ⟨1206372866470135815, 1206522790122734419⟩, true⟩

def words01 : List Nat := [371285722194884420, 371285721448459694, 371285720927427178, 371285720928307784, 371285720378745173, 371285720185039690, 371285719991094056, 371285719542364652, 371285717016319222, 371285715135291023]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362439178351438601, 362439187116486409⟩, ⟨1178044573104261510, 1178194677376912080⟩, true⟩

def words02 : List Nat := [371285713253958401, 371285712930719582, 371285711217651499, 371285709364553347, 371285707511300268, 371285706115996237, 371285704196270207, 371285703106856209, 371285702017248992, 371285700921357192]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470511762570423, 362470520534845065⟩, ⟨384150164832238543, 384300452197885431⟩, true⟩

def words03 : List Nat := [371285699085660415, 371285698588917632, 371285698091823371, 371285697706980111, 371285695505912757, 371285693014217901, 371285690522391033, 371285689049793513, 371285686896155135, 371285686298546640]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362455623394996314, 362455632174500060⟩, ⟨761348044682946567, 761498515269402787⟩, true⟩

def words04 : List Nat := [371285685700678146, 371285685097370975, 371285682420737215, 371285681299710234, 371285680178350814, 371285679268877798, 371285677314242613, 371285674879179345, 371285672443990940, 371285671563662562]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452724923193258, 362452733709907520⟩, ⟨834990407319728589, 835141060730584349⟩, true⟩

def words05 : List Nat := [371285670480876369, 371285670583352710, 371285670688242345, 371285670689057019, 371285669504846537, 371285668391542601, 371285667717324994, 371285667718126650, 371285666437446393, 371285665139747055]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481623268815420, 362481632062714229⟩, ⟨101989228989875685, 102140064637659149⟩, true⟩

def words06 : List Nat := [371285663841793942, 371285663187635476, 371285661754928853, 371285661340562732, 371285660925987137, 371285660309257207, 371285658308207841, 371285657860082232, 371285658079410478, 371285658080240349]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469821907877846, 362469830709074609⟩, ⟨401562467136838829, 401713487970434689⟩, true⟩

def words07 : List Nat := [371285657922159931, 371285657777107845, 371285659037392994, 371285659671359882, 371285660238547102, 371285660806000038, 371285661079560772, 371285661080362500, 371285659286353866, 371285658663683374]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462563995414689, 362462572803762111⟩, ⟨585907251149598001, 586058453504068829⟩, true⟩

def words08 : List Nat := [371285658388919292, 371285658389735545, 371285657591114683, 371285656787062552, 371285655982758990, 371285655650692980, 371285654763146408, 371285654980736371, 371285655057894916, 371285655058724855]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362516094813210626, 362516103628816356⟩, ⟨(-773442587456743578), (-773291200777498484)⟩, true⟩

def words09 : List Nat := [371285654790299523, 371285655431321939, 371285657361738624, 371285657362540724, 371285657228360724, 371285656857075967, 371285657482770333, 371285657893244317, 371285659092443932, 371285660291909247]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk253
