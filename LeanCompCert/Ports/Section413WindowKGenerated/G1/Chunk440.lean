import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507413699004365, 362507441384266209⟩, ⟨(-964475856177198993), (-963652795192008009)⟩, true⟩

def state01 : KState := ⟨⟨362486928319513311, 362486956017904305⟩, ⟨(-63014388202416502), (-62190749466711734)⟩, true⟩

def words00 : List Nat := [371285541177682800, 371285541251921088, 371285541775605796, 371285542300006537, 371285542930124635, 371285542931578959, 371285542873583650, 371285542815321634, 371285542911265181, 371285542945048276]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475666605436400, 362475694316910135⟩, ⟨432707089745680955, 433531304319594833⟩, true⟩

def words01 : List Nat := [371285543243226288, 371285543541961700, 371285543778154102, 371285543779608903, 371285543399889815, 371285543176555581, 371285543243391317, 371285543244852831, 371285543046616766, 371285542824504856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362502917835390779, 362502945559901980⟩, ⟨(-767013564422240873), (-766188775872700301)⟩, true⟩

def words02 : List Nat := [371285542894065257, 371285543072524250, 371285543378279639, 371285543684605631, 371285543893199681, 371285543894654776, 371285543451437753, 371285543489037709, 371285544041765280, 371285544438513125]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497876868547631, 362497904606317148⟩, ⟨(-545004016557046846), (-544178644177068274)⟩, true⟩

def words03 : List Nat := [371285544837285531, 371285545236546712, 371285545899996776, 371285546338975714, 371285546932851898, 371285547527244661, 371285548004579466, 371285548006035307, 371285548141192298, 371285548423574316]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489743476260662, 362489771227006812⟩, ⟨(-186688457220020021), (-185862513281656827)⟩, true⟩

def words04 : List Nat := [371285549220708055, 371285549531541817, 371285549831776146, 371285550132519764, 371285550491655835, 371285550595768645, 371285551021307751, 371285551447435012, 371285551872188668, 371285551969480726]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508924799080077, 362508952562974533⟩, ⟨(-1031784186228224419), (-1030957663038400883)⟩, true⟩

def words05 : List Nat := [371285552171838067, 371285552374904221, 371285553092554078, 371285553123961631, 371285553125106731, 371285552993142181, 371285553063412174, 371285553080961307, 371285553613031759, 371285554145711230]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492985617396742, 362493013394435719⟩, ⟨(-329511903107809655), (-328684800706269577)⟩, true⟩

def words06 : List Nat := [371285554662025412, 371285554663481714, 371285554792512007, 371285555093566591, 371285555417318699, 371285555418784905, 371285555282261183, 371285555090665292, 371285555149047773, 371285555319948953]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463172183714518, 362463199973892822⟩, ⟨984657568450286520, 985485249969174336⟩, true⟩

def words07 : List Nat := [371285556005082869, 371285556690817726, 371285557342691312, 371285557344148200, 371285557326070101, 371285557344022075, 371285557625625164, 371285557627082151, 371285557222849879, 371285556717313176]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495668962370382, 362495696765587889⟩, ⟨(-447954394573438362), (-447126138220003876)⟩, true⟩

def words08 : List Nat := [371285556211130585, 371285556027578786, 371285555632043401, 371285555573272411, 371285555514064184, 371285555377532783, 371285554948288731, 371285554992193520, 371285555549785468, 371285555781300393]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482117486624125, 362482145303145924⟩, ⟨149635278384425209, 150464121387536429⟩, true⟩

def words09 : List Nat := [371285555954190740, 371285556127538819, 371285556514057817, 371285556645077881, 371285556930472814, 371285557216440726, 371285557500850582, 371285557502312166, 371285557263515234, 371285557187984644]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440
