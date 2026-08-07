import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk470

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504758762353436, 362504790521451463⟩, ⟨(-913741394763449201), (-912732901073180137)⟩, true⟩

def state01 : KState := ⟨⟨362476975149908687, 362477006923086293⟩, ⟨392156493375931387, 393165648879719391⟩, true⟩

def words00 : List Nat := [371285371501256663, 371285371502818560, 371285371479376154, 371285371586359519, 371285371648293716, 371285371649858975, 371285371243076626, 371285370838345481, 371285370432968290, 371285370370201369]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471063447974978, 362471095235215130⟩, ⟨670208099644876136, 671217916302121992⟩, true⟩

def words01 : List Nat := [371285370401019473, 371285370610384580, 371285370820573383, 371285370822146157, 371285370625537458, 371285370568210798, 371285370902109165, 371285370903671533, 371285370694805956, 371285370392941675]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486442868045449, 362486474669269622⟩, ⟨(-52954692080727990), (-51944217822661724)⟩, true⟩

def words02 : List Nat := [371285370090416125, 371285370087797828, 371285370083636912, 371285370265680050, 371285370341857191, 371285370343446991, 371285370043480422, 371285369954407479, 371285370176522455, 371285370201624396]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479507408076032, 362479539223588600⟩, ⟨273273206155853453, 274284352464997183⟩, true⟩

def words03 : List Nat := [371285370202793419, 371285370194868658, 371285370365824608, 371285370393630444, 371285370471879175, 371285370550717673, 371285370630402814, 371285370631967336, 371285370220393790, 371285370098428418]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456199804286095, 362456231633701139⟩, ⟨1369866943499224949, 1370878743854921785⟩, true⟩

def words04 : List Nat := [371285370302397484, 371285370303961332, 371285370106119089, 371285369906817455, 371285369706937371, 371285369601494806, 371285369268833231, 371285368935680416, 371285368602001235, 371285368270127387]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362511420785868778, 362511452629409447⟩, ⟨(-1228563674544507211), (-1227551209506968213)⟩, true⟩

def words05 : List Nat := [371285367651932131, 371285367485202232, 371285367539267239, 371285367540857926, 371285367387968895, 371285367161150787, 371285367155701248, 371285367261216321, 371285367816578040, 371285368372604302]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478545754214182, 362478577611886568⟩, ⟨318647251756889177, 319660381904674071⟩, true⟩

def words06 : List Nat := [371285368852762623, 371285368854326695, 371285368944954976, 371285369158431758, 371285369509211898, 371285369510776188, 371285369304467345, 371285369056634171, 371285368808167814, 371285368782099117]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362459011692644893, 362459043564404646⟩, ⟨1238303500143605475, 1239317293456603367⟩, true⟩

def words07 : List Nat := [371285368894175511, 371285369151173050, 371285369375834375, 371285369377398759, 371285369001360749, 371285368641249148, 371285368323368786, 371285368324933273, 371285367768604515, 371285367211249519]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482573199225140, 362482605085016808⟩, ⟨128980739444144779, 129995193448418891⟩, true⟩

def words08 : List Nat := [371285366653199011, 371285366383264468, 371285366001145002, 371285366019214618, 371285366020426594, 371285365989875024, 371285365527562742, 371285365516023884, 371285365652376335, 371285365654000636]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482950309399787, 362482982209421720⟩, ⟨111264651870108729, 112279776049928507⟩, true⟩

def words09 : List Nat := [371285365596557047, 371285365445019594, 371285365589469764, 371285365705150874, 371285365958425193, 371285366212332075, 371285366464188880, 371285366465754334, 371285366117477214, 371285366068785838]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk470
