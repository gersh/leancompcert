import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk703

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551207841750838, 360551239704873427⟩, ⟨2195647503211980443, 2197160523474873413⟩, true⟩

def state01 : KState := ⟨⟨360567383474489666, 360567415347026806⟩, ⟨1058334460585381593, 1059848142736135655⟩, true⟩

def words00 : List Nat := [360582493322623801, 360582492765433696, 360582492309926903, 360582492016137077, 360582491722274057, 360582491257960244, 360582490591442489, 360582490086750685, 360582489581749572, 360582489278796628]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550634492688196, 360550666374708097⟩, ⟨2236073590253360459, 2237587939184435363⟩, true⟩

def words01 : List Nat := [360582489065296158, 360582488722664152, 360582488379841518, 360582488239115817, 360582488200051284, 360582487992365259, 360582487784589302, 360582487445795912, 360582486904853384, 360582486453479207]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563444572986401, 360563476464402890⟩, ⟨1335213708666840179, 1336728718413404525⟩, true⟩

def words02 : List Nat := [360582486001787156, 360582485752065285, 360582485507727336, 360582485109179825, 360582484710483069, 360582484198932374, 360582483788392670, 360582483579780146, 360582483371082870, 360582482986774757]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600507692496848, 360600539593314286⟩, ⟨(-1271634649941832056), (-1270118978979606458)⟩, true⟩

def words03 : List Nat := [360582482717336722, 360582482589474696, 360582482475364622, 360582482543565693, 360582482544494263, 360582482439868832, 360582482346795767, 360582482482632476, 360582482740150630, 360582482997886590]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576452667891649, 360576484578214061⟩, ⟨420338441646048142, 421854781234389162⟩, true⟩

def words04 : List Nat := [360582483154591199, 360582483155587704, 360582483110363029, 360582482981541344, 360582482852454668, 360582482590237030, 360582482261525678, 360582481819569563, 360582481377434932, 360582481092517322]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360545817642892357, 360545849562597195⟩, ⟨2575780393886435195, 2577297393574873213⟩, true⟩

def words05 : List Nat := [360582481124421505, 360582481241750241, 360582481257562511, 360582481258560081, 360582481168249011, 360582481027547471, 360582480886561423, 360582480636293867, 360582480232745729, 360582479713159658]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558269005814112, 360558300934926690⟩, ⟨1699667794040903042, 1701185455704950538⟩, true⟩

def words06 : List Nat := [360582479193362718, 360582478818275324, 360582478544822630, 360582478340832392, 360582478136753028, 360582477760614365, 360582477232204543, 360582476736037844, 360582476239596657, 360582475802849171]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581175409742444, 360581207348372719⟩, ⟨87558295537945580, 89076627007132786⟩, true⟩

def words07 : List Nat := [360582475460226978, 360582474963839708, 360582474467275607, 360582474172449851, 360582474007232822, 360582473783893086, 360582473560449054, 360582473236342845, 360582473017761183, 360582473000930366]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581523197449334, 360581555145461936⟩, ⟨63105640352059437, 64624632197103673⟩, true⟩

def words08 : List Nat := [360582473167163777, 360582473292781305, 360582473293670589, 360582473292290493, 360582473290762122, 360582473149486926, 360582473204872181, 360582473301064230, 360582473301968187, 360582473239398534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586086027042437, 360586117984485838⟩, ⟨(-258045984808807132), (-256526329083340296)⟩, true⟩

def words09 : List Nat := [360582473345002883, 360582473463958038, 360582473783924826, 360582473967561395, 360582473985723681, 360582474003956524, 360582474004765432, 360582474090963275, 360582474143543644, 360582474196342441]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk703
