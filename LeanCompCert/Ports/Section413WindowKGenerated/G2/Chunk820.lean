import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk820

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574281939940936, 360574325820400155⟩, ⟨651014260065630362, 653444329874095360⟩, true⟩

def state01 : KState := ⟨⟨360609205617569529, 360609249509119732⟩, ⟨(-2212919040757849518), (-2210488061435555328)⟩, true⟩

def words00 : List Nat := [360582294557461734, 360582294639229261, 360582294871060881, 360582295103120222, 360582295179357847, 360582295180532983, 360582295252759125, 360582295364004791, 360582295623481141, 360582295953359706]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602536755594624, 360602580658347078⟩, ⟨(-1665933363435738309), (-1663501465360684673)⟩, true⟩

def words01 : List Nat := [360582296208586563, 360582296463956939, 360582296867655035, 360582297346266769, 360582297762122830, 360582298178168110, 360582298499843945, 360582298752269110, 360582299000515778, 360582299249130406]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597581259641232, 360597625173466374⟩, ⟨(-1259477323611019470), (-1257044517300083036)⟩, true⟩

def words02 : List Nat := [360582299645903504, 360582299894604845, 360582300051441418, 360582300208400064, 360582300275439675, 360582300455887304, 360582300658264616, 360582300860855727, 360582300967473624, 360582301155506090]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620440107790547, 360620484032716211⟩, ⟨(-3134768460238560199), (-3132334743295781379)⟩, true⟩

def words03 : List Nat := [360582301491786071, 360582301828403000, 360582302160739807, 360582302345020405, 360582302403005232, 360582302461069765, 360582302667410845, 360582302985618850, 360582303451964606, 360582303918586742]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602124826116941, 360602168762238708⟩, ⟨(-1632148207973898904), (-1629713572448777752)⟩, true⟩

def words04 : List Nat := [360582304262778427, 360582304633543623, 360582305048395741, 360582305463591363, 360582305816656317, 360582306021677187, 360582306112470650, 360582306203371800, 360582306316381015, 360582306559798168]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595112051032148, 360595155998224163⟩, ⟨(-1056633006764074448), (-1054197462868982910)⟩, true⟩

def words05 : List Nat := [360582306951273037, 360582307342963747, 360582307658527681, 360582307977729462, 360582308259443596, 360582308541468776, 360582308912285675, 360582309172773771, 360582309330378335, 360582309488153984]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608312525398069, 360608356483700746⟩, ⟨(-2139947340631878234), (-2137510884941339496)⟩, true⟩

def words06 : List Nat := [360582309595301009, 360582309800181361, 360582310120817866, 360582310441673489, 360582310635827311, 360582310744028307, 360582311000400179, 360582311257133607, 360582311510081377, 360582311828646692]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599465097547837, 360599509067054102⟩, ⟨(-1413793323874864574), (-1411355948650982880)⟩, true⟩

def words07 : List Nat := [360582312033461337, 360582312238382164, 360582312591457298, 360582313019310148, 360582313334620697, 360582313650099939, 360582313885456920, 360582313972837685, 360582314183280405, 360582314394125520]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360611028789826837, 360611072770424006⟩, ⟨(-2362928274773114178), (-2360489989152186116)⟩, true⟩

def words08 : List Nat := [360582314716645740, 360582315172414914, 360582315553643074, 360582315934990166, 360582316278898749, 360582316697509884, 360582317125021318, 360582317552746782, 360582317866183407, 360582318217681901]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360608215667574959, 360608259659276702⟩, ⟨(-2132003119651673260), (-2129563922400639312)⟩, true⟩

def words09 : List Nat := [360582318682211837, 360582319147075815, 360582319564531021, 360582319834160975, 360582319976055052, 360582320118052382, 360582320362572298, 360582320681934268, 360582320998832023, 360582321315987332]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk820
