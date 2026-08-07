import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk131

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360732179214143774, 360732180172167916⟩, ⟨(-1978020927678445401), (-1978012427233652947)⟩, true⟩

def state01 : KState := ⟨⟨360668277012431928, 360668277971996782⟩, ⟨(-1141354867350854993), (-1141346346715123597)⟩, true⟩

def words00 : List Nat := [360581205423834570, 360581206689203857, 360581213757114957, 360581220823999779, 360581226365681218, 360581226365843010, 360581226133467737, 360581221740265402, 360581218753908524, 360581225394259377]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360521382427151123, 360521383388242139⟩, ⟨785120434744893241, 785128975396372951⟩, true⟩

def words01 : List Nat := [360581231832430206, 360581238269648790, 360581241201703789, 360581241201865744, 360581240628538501, 360581237136828720, 360581233645604911, 360581231744565522, 360581230097076448, 360581225535757107]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360654398126780545, 360654399089400824⟩, ⟨(-960717430948594961), (-960708870225655077)⟩, true⟩

def words02 : List Nat := [360581222201965171, 360581226332427130, 360581231255269690, 360581236177392544, 360581236177544481, 360581235608867139, 360581229287114862, 360581228748123562, 360581230096831379, 360581235669232851]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360535266398050808, 360535267362217479⟩, ⟨604378365569117000, 604386946603823746⟩, true⟩

def words03 : List Nat := [360581238270744385, 360581240871878941, 360581245953069268, 360581255321416122, 360581261507158842, 360581267691986211, 360581270132179289, 360581270132341550, 360581266825202218, 360581263324668303]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360501991829618482, 360501992795313973⟩, ⟨1041371209652956805, 1041379810784085041⟩, true⟩

def words04 : List Nat := [360581259824612650, 360581258151122092, 360581250732654783, 360581239540332144, 360581228349686751, 360581213252047567, 360581202634525122, 360581197783044696, 360581192932285557, 360581185176362193]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611832693424883, 360611833660656144⟩, ⟨(-403925276918204193), (-403916655584287869)⟩, true⟩

def words05 : List Nat := [360581179154717337, 360581178895804513, 360581178636886112, 360581178188715452, 360581172002954463, 360581160894368754, 360581149787438780, 360581141995548037, 360581140905501598, 360581143237771539]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360523683474762997, 360523684443541223⟩, ⟨756058407687150632, 756067049386895562⟩, true⟩

def words06 : List Nat := [360581143237916435, 360581141859613598, 360581134749061361, 360581133392217811, 360581132035537703, 360581129156943918, 360581123713095773, 360581112855411004, 360581101999344887, 360581092723676903]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360530270956948556, 360530271927258494⟩, ⟨669569635815429156, 669578297695508978⟩, true⟩

def words07 : List Nat := [360581089752023996, 360581091138879620, 360581091139024578, 360581089624671927, 360581088367940291, 360581083160631672, 360581078488073513, 360581078488237307, 360581078384157863, 360581074529511568]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360655848828752927, 360655849800601011⟩, ⟨(-986147429569803233), (-986138747409366511)⟩, true⟩

def words08 : List Nat := [360581070675415864, 360581066338296688, 360581070635308025, 360581075651300225, 360581075849777224, 360581075849940372, 360581077706633321, 360581081501459975, 360581085680083168, 360581091348064482]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566846175838679, 360566847149237491⟩, ⟨188344230284739742, 188352932906888434⟩, true⟩

def words09 : List Nat := [360581094121861669, 360581096895256585, 360581103438651391, 360581112900939578, 360581117124177646, 360581121346799238, 360581122217315256, 360581122217478279, 360581117391713460, 360581116310821347]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk131
