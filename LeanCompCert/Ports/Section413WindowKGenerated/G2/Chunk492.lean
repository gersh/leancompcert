import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk492

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587516170059109, 360587531335731012⟩, ⟨(-278251759400573337), (-277747570225768349)⟩, true⟩

def state01 : KState := ⟨⟨360601035181274641, 360601050353338071⟩, ⟨(-943548436171482084), (-943043932502519282)⟩, true⟩

def words00 : List Nat := [360581886701755407, 360581886944853561, 360581886945477764, 360581886788415482, 360581886631251662, 360581886242905900, 360581886382397494, 360581886658413742, 360581886688072323, 360581887078206444]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360633179199636019, 360633194378098340⟩, ⟨(-2525505339623813109), (-2525000521033506245)⟩, true⟩

def words01 : List Nat := [360581887879869079, 360581888681704911, 360581889707566613, 360581890675460340, 360581891252466548, 360581891829500704, 360581892303643357, 360581893039537347, 360581894082372187, 360581895125319374]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360609301669219621, 360609316854143241⟩, ⟨(-1350280597269685283), (-1349775460622172323)⟩, true⟩

def words02 : List Nat := [360581895960297172, 360581896383015095, 360581897217085649, 360581898051334105, 360581898610438122, 360581898878766120, 360581898896654035, 360581898914615846, 360581899110916483, 360581899668617411]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570847471966028, 360570862663285322⟩, ⟨542952880502360771, 543458332041390555⟩, true⟩

def words03 : List Nat := [360581900046052640, 360581900423592275, 360581900595271434, 360581900595949996, 360581900477525877, 360581900168318198, 360581899858919308, 360581899830025213, 360581899814678687, 360581899591230923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574206126222049, 360574221323947927⟩, ⟨377627946067126862, 378133713097350222⟩, true⟩

def words04 : List Nat := [360581899385081170, 360581899652388802, 360581900112661499, 360581900573047978, 360581900623515101, 360581900624193766, 360581900262720307, 360581899850111611, 360581899437312925, 360581899165838229]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360567755720834325, 360567770925027346⟩, ⟨695410876389933724, 695916961959988978⟩, true⟩

def words05 : List Nat := [360581899010550614, 360581898649787280, 360581898338421690, 360581898597105805, 360581898753540464, 360581898910079826, 360581898910692860, 360581898802663347, 360581898636183429, 360581898350158487]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571617496605397, 360571632707192422⟩, ⟨505128459146934908, 505634859716645830⟩, true⟩

def words06 : List Nat := [360581898187977137, 360581898188655965, 360581897901747932, 360581897409517777, 360581896917196962, 360581896230933434, 360581895927001242, 360581895801748146, 360581895676429937, 360581895237326716]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604378626659227, 360604393843659488⟩, ⟨(-1109304709079146949), (-1108797992497433569)⟩, true⟩

def words07 : List Nat := [360581895045560490, 360581895062279657, 360581895070369880, 360581895071049004, 360581894807180169, 360581894194763117, 360581893582240779, 360581893426544334, 360581893883676413, 360581894340960732]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575333170868181, 360575348394330069⟩, ⟨322031989920319353, 322539024962622967⟩, true⟩

def words08 : List Nat := [360581894592857509, 360581894615678958, 360581894616232036, 360581894538578322, 360581894460740598, 360581894281069695, 360581893925939886, 360581893251340259, 360581892576638505, 360581892095384292]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556839815375125, 360556855045231454⟩, ⟨1233706542728921188, 1234213892985361474⟩, true⟩

def words09 : List Nat := [360581891963180593, 360581891893954343, 360581891824662223, 360581891547680748, 360581891289230085, 360581890929166583, 360581890618331518, 360581890619010890, 360581890316903460, 360581889809795052]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk492
