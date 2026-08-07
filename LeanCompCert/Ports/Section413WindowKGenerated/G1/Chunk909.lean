import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk909

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470822715205130, 362470947842530280⟩, ⟨1279777647573803806, 1287457195067028198⟩, true⟩

def state01 : KState := ⟨⟨362473642585431872, 362473767741042109⟩, ⟨1023483176160045092, 1031165294914809892⟩, true⟩

def words00 : List Nat := [371285111134360881, 371285111102710170, 371285110984131068, 371285110864708213, 371285110744019809, 371285110661654073, 371285110523341750, 371285110507206844, 371285110490108187, 371285110445859124]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488973994879809, 362489099179218775⟩, ⟨(-370351008693535168), (-362666278065592852)⟩, true⟩

def words01 : List Nat := [371285110323244409, 371285110323229866, 371285110424464773, 371285110427639311, 371285110383932403, 371285110313633134, 371285110289112195, 371285110292643887, 371285110325225996, 371285110372693709]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483547700225286, 362483672913234345⟩, ⟨122990758542177288, 130678096006044934⟩, true⟩

def words02 : List Nat := [371285110418872100, 371285110422062250, 371285110356661636, 371285110332439696, 371285110315401173, 371285110318597720, 371285110221399114, 371285110125488730, 371285110038065185, 371285110041750853]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472275916088975, 362472401157633359⟩, ⟨1148053549049901365, 1155743481378653123⟩, true⟩

def words03 : List Nat := [371285110133154522, 371285110241624789, 371285110334687797, 371285110337870092, 371285110305711810, 371285110295975367, 371285110285251450, 371285110288428386, 371285110151130461, 371285110014917048]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489625754694707, 362489751024688235⟩, ⟨(-429805553810769523), (-422113034180298977)⟩, true⟩

def words04 : List Nat := [371285109877322058, 371285109851991070, 371285109811663737, 371285109852436831, 371285109873461393, 371285109876639005, 371285109756893260, 371285109759630307, 371285109866530670, 371285109920861117]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491609526006916, 362491734824990042⟩, ⟨(-610241090009462089), (-602545933627693831)⟩, true⟩

def words05 : List Nat := [371285109944101980, 371285109968401577, 371285110079922458, 371285110141895684, 371285110239524583, 371285110338339842, 371285110436043013, 371285110450349608, 371285110525345460, 371285110602151379]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481240757853310, 362481366085090390⟩, ⟨332950057411841660, 340647783923486410⟩, true⟩

def words06 : List Nat := [371285110757821411, 371285110760997979, 371285110755863254, 371285110753157379, 371285110749305540, 371285110742817417, 371285110680674788, 371285110690169759, 371285110698508997, 371285110701820340]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496420285300509, 362496545641261508⟩, ⟨(-1047976907918082252), (-1040276568246671332)⟩, true⟩

def words07 : List Nat := [371285110742385498, 371285110825835223, 371285110997430836, 371285111054089658, 371285111090518042, 371285111127977152, 371285111284818428, 371285111386215611, 371285111514087399, 371285111643303180]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490721748941748, 362490847133586641⟩, ⟨(-529555128305617427), (-521852178828961285)⟩, true⟩

def words08 : List Nat := [371285111746723119, 371285111749900452, 371285111726943552, 371285111765632039, 371285111830388576, 371285111833622236, 371285111812052667, 371285111789485406, 371285111860346598, 371285111927040621]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482886573467413, 362483011986795633⟩, ⟨183435752155690685, 191141311668235043⟩, true⟩

def words09 : List Nat := [371285112080756924, 371285112235825722, 371285112366329465, 371285112369507110, 371285112343030297, 371285112350930498, 371285112477882849, 371285112481060717, 371285112460167941, 371285112440770010]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk909
