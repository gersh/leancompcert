import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk533

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501874491464364, 362501915752926792⟩, ⟨(-901817582982578423), (-900331870922747191)⟩, true⟩

def state01 : KState := ⟨⟨362495361859672513, 362495403137233952⟩, ⟨(-554727814569474478), (-553241244347121562)⟩, true⟩

def words00 : List Nat := [371285024594998181, 371285024596787749, 371285024753277701, 371285024987316084, 371285025235233567, 371285025237033775, 371285025170467987, 371285025104552446, 371285025321569626, 371285025518274505]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483031966000296, 362483073259715976⟩, ⟨102757391403650042, 104244822887469558⟩, true⟩

def words01 : List Nat := [371285026015876810, 371285026514252424, 371285027003860144, 371285027226832066, 371285027557387941, 371285027888814774, 371285028337200693, 371285028372194530, 371285028373555383, 371285028338914916]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362514121911750225, 362514163221480617⟩, ⟨(-1555054461813068779), (-1553566176342694379)⟩, true⟩

def words02 : List Nat := [371285028572094215, 371285028667042533, 371285029112528168, 371285029558707670, 371285029957929130, 371285030158288858, 371285030709277753, 371285031261210613, 371285032033123283, 371285032581208680]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492513641310088, 362492554967338009⟩, ⟨(-402527561554413191), (-401038406853899679)⟩, true⟩

def words03 : List Nat := [371285033101184846, 371285033621727605, 371285034228359539, 371285034659780463, 371285035198482904, 371285035737865648, 371285036249113798, 371285036292606513, 371285036434792427, 371285036577977969]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480413226935488, 362480454568887668⟩, ⟨242982943616379603, 244472947800465531⟩, true⟩

def words04 : List Nat := [371285036986497125, 371285036988286840, 371285036966661250, 371285036945879235, 371285036966811375, 371285036968788770, 371285036911813085, 371285036957602767, 371285037002780298, 371285037004647752]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362524287649289085, 362524329007440450⟩, ⟨(-2097929910785378018), (-2096439042296970784)⟩, true⟩

def words05 : List Nat := [371285037129030442, 371285037340275792, 371285037901438554, 371285038216227714, 371285038473150690, 371285038730604384, 371285039292670062, 371285039680130640, 371285040417652205, 371285041155970332]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491948669981003, 362491990044309304⟩, ⟨(-372263740708122950), (-370772008934713064)⟩, true⟩

def words06 : List Nat := [371285041774432253, 371285041925514704, 371285042235246457, 371285042545869897, 371285042915834851, 371285042917625293, 371285042819944737, 371285042722879916, 371285042843280208, 371285042975509119]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480340315342093, 362480381705773914⟩, ⟨247369673452775138, 248862264752642730⟩, true⟩

def words07 : List Nat := [371285043331375323, 371285043687949556, 371285044043901591, 371285044045692180, 371285043934028601, 371285043829544590, 371285043968039367, 371285043969838528, 371285043879250774, 371285043793910907]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483603047379161, 362483644453852347⟩, ⟨73274145776798963, 74767593447571521⟩, true⟩

def words08 : List Nat := [371285043970998680, 371285044127774016, 371285044387929138, 371285044648808095, 371285044852078652, 371285044853869839, 371285044652419425, 371285044717382768, 371285044856441642, 371285044858299764]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483425985174963, 362483467407986059⟩, ⟨82764395568695521, 84258715601960711⟩, true⟩

def words09 : List Nat := [371285044833417189, 371285044774111361, 371285044969766189, 371285045102416386, 371285045296768074, 371285045491814629, 371285045635593825, 371285045637385510, 371285045313866992, 371285045286555385]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk533
