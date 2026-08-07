import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk470

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360616604698858572, 360616618486653953⟩, ⟨(-1584430584117501591), (-1583992683031650287)⟩, true⟩

def state01 : KState := ⟨⟨360585810838327707, 360585824632268319⟩, ⟨(-137150129297147284), (-136711939354408062)⟩, true⟩

def words00 : List Nat := [360582917724012093, 360582917917054171, 360582918181450792, 360582918446021973, 360582918446573232, 360582918295414181, 360582917950674151, 360582917380104733, 360582916809433328, 360582916548216621]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564809492233802, 360564823292261054⟩, ⟨850349345741384092, 850787821848412600⟩, true⟩

def words01 : List Nat := [360582916921081025, 360582917294065314, 360582917441871886, 360582917523232741, 360582917523773267, 360582917491598214, 360582917877188193, 360582917877834138, 360582917845322833, 360582917461164679]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601869778690809, 360601883584815305⟩, ⟨(-892405420237724743), (-891966657408509479)⟩, true⟩

def words02 : List Nat := [360582917076879052, 360582916889994825, 360582917252463104, 360582917615039632, 360582917615646732, 360582917553850913, 360582917507108644, 360582917447656618, 360582917676057935, 360582918079990647]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577553271196180, 360577567083484801⟩, ⟨251308422646317628, 251747475404443256⟩, true⟩

def words03 : List Nat := [360582918208253915, 360582918336582289, 360582918454324101, 360582918889654044, 360582919080706071, 360582919271859005, 360582919272434646, 360582919238704190, 360582918971070422, 360582918858046971]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360555905169804126, 360555918988173401⟩, ⟨1269805266125329041, 1270244604948555791⟩, true⟩

def words04 : List Nat := [360582919081401663, 360582919148222749, 360582919148803787, 360582918986660431, 360582918824417189, 360582918489810066, 360582918381621320, 360582917912023752, 360582917442375532, 360582916748108546]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360635618565505667, 360635632389977363⟩, ⟨(-2481170393239168420), (-2480730767267416628)⟩, true⟩

def words05 : List Nat := [360582916174833414, 360582916051942031, 360582916150227957, 360582916387024021, 360582916387620030, 360582916237572035, 360582916386782115, 360582917057660296, 360582918178355832, 360582919299153382]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594461941371681, 360594475772011570⟩, ⟨(-544301881176297837), (-543861964899369425)⟩, true⟩

def words06 : List Nat := [360582920075155696, 360582920401145712, 360582920926537242, 360582921452095431, 360582921864057898, 360582921964403986, 360582921964980469, 360582921776423790, 360582921587743373, 360582921694874918]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360542470153751054, 360542483990476974⟩, ⟨1903294029933844547, 1903734232711123919⟩, true⟩

def words07 : List Nat := [360582922280584300, 360582922866392662, 360582923101838821, 360582923102485650, 360582922888087527, 360582922351555888, 360582921814857514, 360582921634780058, 360582921004877890, 360582920146651807]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589229547736693, 360589243390577092⟩, ⟨(-298338786881445649), (-297898296205071797)⟩, true⟩

def words08 : List Nat := [360582919288311991, 360582918572092960, 360582918271876595, 360582918303120176, 360582918303716882, 360582917945573184, 360582917456740189, 360582917417549492, 360582917378173123, 360582917377194385]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575720169402598, 360575734018400512⟩, ⟨337933897161747604, 338374677826524208⟩, true⟩

def words09 : List Nat := [360582917377774579, 360582917162185050, 360582917179604555, 360582917684423910, 360582918076030866, 360582918467738588, 360582918631261091, 360582918631908270, 360582918345945355, 360582918194150545]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk470
