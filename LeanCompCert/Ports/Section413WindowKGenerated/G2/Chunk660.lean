import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578835439515061, 360578863383381892⟩, ⟨268173665615986354, 269419493096494586⟩, true⟩

def state01 : KState := ⟨⟨360583043130144772, 360583071082784215⟩, ⟨(-9667457817108099), (-8421051301642033)⟩, true⟩

def words00 : List Nat := [360582945441853424, 360582945442784081, 360582945295280458, 360582944970982342, 360582944646541927, 360582944221079541, 360582943936786259, 360582943832959300, 360582943729033681, 360582943512359564]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591617325948377, 360591645287365887⟩, ⟨(-575763994616627031), (-574517008616751019)⟩, true⟩

def words01 : List Nat := [360582943513119232, 360582943438586050, 360582943472119511, 360582943515253308, 360582943516120562, 360582943358198703, 360582943200116653, 360582943036991934, 360582943120261701, 360582943253034133]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587016141770949, 360587044112055620⟩, ⟨(-272083279647398913), (-270835708194737405)⟩, true⟩

def words02 : List Nat := [360582943253863670, 360582943243983642, 360582943327897992, 360582943457836387, 360582943470860488, 360582943471791317, 360582943256064494, 360582942896090600, 360582942535946983, 360582942467249473]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567493639257419, 360567521618318359⟩, ⟨1017031191794840014, 1018279342788582746⟩, true⟩

def words03 : List Nat := [360582942524872172, 360582942582658227, 360582942583503043, 360582942431821899, 360582942108107579, 360582941695423062, 360582941282478018, 360582941098698689, 360582940980798742, 360582940748281845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603672530626964, 360603700518475290⟩, ⟨(-1372385293542662321), (-1371136562187031201)⟩, true⟩

def words04 : List Nat := [360582940515556554, 360582940624154889, 360582940923942120, 360582941223906873, 360582941272925269, 360582941273856562, 360582941142455556, 360582941191853579, 360582941447681489, 360582941762935071]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360572147594825672, 360572175591560429⟩, ⟨710039463593807376, 711288781942099212⟩, true⟩

def words05 : List Nat := [360582941933438051, 360582942104045673, 360582942342256315, 360582942712550060, 360582942932271679, 360582943152134567, 360582943223825080, 360582943224756524, 360582943067772804, 360582942905849592]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593768750273780, 360593796755784767⟩, ⟨(-718371815430977560), (-717121917283101056)⟩, true⟩

def words06 : List Nat := [360582942743612903, 360582942736501649, 360582942737333637, 360582942601153331, 360582942464825472, 360582942241411913, 360582942454413416, 360582942675842477, 360582942783013608, 360582942948255245]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583579588700407, 360583607603016959⟩, ⟨(-45078775272261421), (-43828295296065215)⟩, true⟩

def words07 : List Nat := [360582943342019866, 360582943736045797, 360582944124589162, 360582944284773517, 360582944285633762, 360582944250575628, 360582944215345372, 360582944330110867, 360582944340908346, 360582944351926691]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593556298935070, 360593584322114360⟩, ⟨(-704476929696690357), (-703225864025866325)⟩, true⟩

def words08 : List Nat := [360582944352756863, 360582944249116042, 360582944308633032, 360582944453360962, 360582944540397718, 360582944541329462, 360582944453989107, 360582944191288048, 360582943928410368, 360582944055451337]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568637897643155, 360568665929599897⟩, ⟨942560416532786381, 943812062349004191⟩, true⟩

def words09 : List Nat := [360582944229149281, 360582944403024751, 360582944462241044, 360582944528010056, 360582944536214179, 360582944544678319, 360582944732637772, 360582944733569643, 360582944693250106, 360582944478198218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk660
