import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550841478536326, 360550851592070086⟩, ⟨1283718223943705408, 1283995055511410880⟩, true⟩

def state01 : KState := ⟨⟨360587384977116032, 360587395095830037⟩, ⟨(-196416107441008022), (-196139066047554118)⟩, true⟩

def words00 : List Nat := [360582554391346744, 360582554053213817, 360582554051029650, 360582553648051909, 360582553245004408, 360582552687000860, 360582552949241656, 360582553384671171, 360582553385173658, 360582553470936859]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602905409251697, 360602915533148906⟩, ⟨(-825386712046231155), (-825109460654972379)⟩, true⟩

def words01 : List Nat := [360582553795914294, 360582554121035376, 360582554300332257, 360582554300881916, 360582554089593076, 360582553310246446, 360582552530824081, 360582552117350734, 360582552515288517, 360582553018387302]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576270209846216, 360576280338986852⟩, ⟨253695560165189970, 253973024045243966⟩, true⟩

def words02 : List Nat := [360582553138266378, 360582553138816046, 360582552652303021, 360582552137267284, 360582551622108150, 360582550954192196, 360582550014014558, 360582548685547040, 360582547357038494, 360582546636150564]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360522748844201387, 360522758978514149⟩, ⟨2423368052104256871, 2423645725637394505⟩, true⟩

def words03 : List Nat := [360582546934725029, 360582547387987379, 360582547452146361, 360582547452698744, 360582547341619727, 360582546793352396, 360582546244953270, 360582545680897690, 360582544511027741, 360582543036867317]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576710593348868, 360576720732853199⟩, ⟨235605460532325672, 235883344556496414⟩, true⟩

def words04 : List Nat := [360582541562655319, 360582540509983884, 360582539843315667, 360582539783741704, 360582539724124466, 360582539076524909, 360582538646742996, 360582538393877785, 360582538140864526, 360582537831362608]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360589100624635880, 360589110769384214⟩, ⟨(-266961083089720524), (-266682986394886434)⟩, true⟩

def words05 : List Nat := [360582537688409621, 360582537074505598, 360582536460526370, 360582536472570054, 360582536478248691, 360582536484016763, 360582536484510118, 360582536026274665, 360582535744434793, 360582535907166940]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590934762728375, 360590944912652786⟩, ⟨(-341378676949022907), (-341100370285749655)⟩, true⟩

def words06 : List Nat := [360582536476797144, 360582536849405646, 360582536916259382, 360582536983165331, 360582536983634873, 360582536560214063, 360582536799007876, 360582537157861881, 360582537212544533, 360582537420348289]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581406788668307, 360581416943796027⟩, ⟨45255840054429714, 45534357841156958⟩, true⟩

def words07 : List Nat := [360582537945306440, 360582538470416619, 360582539172304937, 360582539269603041, 360582539270111059, 360582538838649467, 360582538580951122, 360582539059081274, 360582539059538711, 360582539032456480]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605977585032998, 360605987745407794⟩, ⟨(-952175266060130422), (-951896535322604278)⟩, true⟩

def words08 : List Nat := [360582539005301375, 360582538651597563, 360582537861179629, 360582537676608654, 360582537491899894, 360582537153270158, 360582537103186147, 360582536699123724, 360582536294976052, 360582536819455672]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565721218459618, 360565731384025020⟩, ⟨682131177798780123, 682410119248828061⟩, true⟩

def words09 : List Nat := [360582538003028541, 360582539186648762, 360582539900557192, 360582540010414543, 360582540010876143, 360582539786402901, 360582539942017689, 360582539942568575, 360582539928463621, 360582539515041001]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405
