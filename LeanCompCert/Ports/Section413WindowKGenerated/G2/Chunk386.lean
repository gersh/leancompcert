import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613414457064085, 360613423608132466⟩, ⟨(-1205844817410330160), (-1205606059164911896)⟩, true⟩

def state01 : KState := ⟨⟨360597709157319810, 360597718313360776⟩, ⟨(-599793651194678474), (-599554700983876968)⟩, true⟩

def words00 : List Nat := [360582191574873909, 360582191575395723, 360582191860850367, 360582192338438955, 360582192356181089, 360582192356703007, 360582191910423659, 360582190994295587, 360582190078114013, 360582190233254489]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547073034086197, 360547082195041731⟩, ⟨1355719569461244262, 1355958709448783160⟩, true⟩

def words01 : List Nat := [360582191304710167, 360582192376219372, 360582193041941242, 360582193298973790, 360582193387554547, 360582193476268765, 360582193758787558, 360582193759309583, 360582193375771046, 360582192467166247]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602303304024615, 360602312469908166⟩, ⟨(-777628132362714351), (-777388802031414477)⟩, true⟩

def words02 : List Nat := [360582191558493264, 360582190748789113, 360582190386245530, 360582190224161200, 360582190062043584, 360582189313035793, 360582188781190279, 360582188466112108, 360582188503485574, 360582189024953819]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580929845699247, 360580939016561026⟩, ⟨48090409904904893, 48329932569515235⟩, true⟩

def words03 : List Nat := [360582189144585229, 360582189264270999, 360582189366249069, 360582189875088051, 360582190215785288, 360582190556552577, 360582190557022602, 360582190522838717, 360582189822977991, 360582189791213447]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360540227941269957, 360540237117048053⟩, ⟨1620960913533026809, 1621200626188941375⟩, true⟩

def words04 : List Nat := [360582189949592027, 360582189950114331, 360582189565667297, 360582188671679264, 360582187777652414, 360582186555509430, 360582185736697263, 360582184900648141, 360582184064587394, 360582182799485025]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360619921481051599, 360619930661757366⟩, ⟨(-1459549167250044325), (-1459309264114916073)⟩, true⟩

def words05 : List Nat := [360582181714665649, 360582181297564403, 360582181130173018, 360582181756446553, 360582181809080186, 360582181861747581, 360582181901064316, 360582182419398307, 360582183396236883, 360582184373143132]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582630401080227, 360582639586769106⟩, ⟨(-17946700767700288), (-17706604960866616)⟩, true⟩

def words06 : List Nat := [360582184826833054, 360582185091096832, 360582185461606541, 360582185832255160, 360582185832696593, 360582185604877393, 360582184712288604, 360582183484777066, 360582182257220010, 360582181708644391]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547606112164992, 360547615302772616⟩, ⟨1336733144324531865, 1336973430363763319⟩, true⟩

def words07 : List Nat := [360582182387776935, 360582183066974444, 360582183413044190, 360582183413567043, 360582183313364458, 360582182564806933, 360582181816131255, 360582181734291962, 360582181175970902, 360582180282875092]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593865935728848, 360593875131279360⟩, ⟨(-452723838152614096), (-452483360898402668)⟩, true⟩

def words08 : List Nat := [360582179389707296, 360582179010669551, 360582179563586065, 360582180116575175, 360582180117057122, 360582180098192297, 360582180024026132, 360582180036692503, 360582180037122634, 360582180335050305]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617527137502132, 360617536338033913⟩, ⟨(-1368348834928895252), (-1368108164924916964)⟩, true⟩

def words09 : List Nat := [360582180335520793, 360582180291499833, 360582180868885703, 360582181824195967, 360582182508682745, 360582183193228424, 360582183543172537, 360582183791337396, 360582184705262804, 360582185619320575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386
