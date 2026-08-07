import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk417

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502124849090836, 362502149607426806⟩, ⟨(-711292983504686684), (-710595374228911824)⟩, true⟩

def state01 : KState := ⟨⟨362486158508983100, 362486183279536869⟩, ⟨(-45445697403856193), (-44747578582299113)⟩, true⟩

def words00 : List Nat := [371285109875567567, 371285109876940671, 371285109777079774, 371285109677589933, 371285109616092665, 371285109617644212, 371285109778907083, 371285110115703851, 371285110451969272, 371285110479110548]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505890360459540, 362505915143448556⟩, ⟨(-868598719957646720), (-867900082400682316)⟩, true⟩

def words01 : List Nat := [371285110992713047, 371285111507030000, 371285112151970915, 371285112153343201, 371285112033029057, 371285111811472083, 371285111742235742, 371285111743751513, 371285112167697460, 371285112667899057]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487789737915217, 362487814533284805⟩, ⟨(-113441186072640441), (-112742031935859819)⟩, true⟩

def words02 : List Nat := [371285113167618199, 371285113168992711, 371285113226574126, 371285113403993402, 371285113759989661, 371285113761363361, 371285113473107500, 371285113067914602, 371285112829533034, 371285112895846550]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490699164632288, 362490723972339398⟩, ⟨(-234774686293856167), (-234075017248235895)⟩, true⟩

def words03 : List Nat := [371285113381487193, 371285113867649145, 371285114351831090, 371285114525270348, 371285114748425360, 371285114972258018, 371285115769186746, 371285115904969788, 371285116040353729, 371285116176233693]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484816496594514, 362484841316614435⟩, ⟨10782716554857313, 11482899599053111⟩, true⟩

def words04 : List Nat := [371285116459728156, 371285116461256438, 371285116734339700, 371285117009376731, 371285117074913054, 371285117076286511, 371285116377485646, 371285116197906570, 371285116354702440, 371285116356125790]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486145702126340, 362486170534684150⟩, ⟨(-44692999690280000), (-43992293128642604)⟩, true⟩

def words05 : List Nat := [371285116350574705, 371285116344288316, 371285116797878810, 371285116972911664, 371285117176888687, 371285117381369397, 371285117598126583, 371285117599500389, 371285117077650630, 371285117104614740]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482625046148760, 362482649890954602⟩, ⟨102479806832790004, 103181024936360698⟩, true⟩

def words06 : List Nat := [371285117703954329, 371285117944305452, 371285118184138097, 371285118424410753, 371285118836318030, 371285118962034535, 371285119381718687, 371285119801949027, 371285120107989014, 371285120109411303]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362522662662078401, 362522687519287306⟩, ⟨(-1570085888862776546), (-1569384152619369506)⟩, true⟩

def words07 : List Nat := [371285120564953337, 371285121080304102, 371285122045139330, 371285122247234883, 371285122340461450, 371285122434153731, 371285123099938192, 371285123569562695, 371285124469585066, 371285125370161642]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488492092464785, 362488516962086030⟩, ⟨(-142304475238618803), (-141602220343358819)⟩, true⟩

def words08 : List Nat := [371285126254188280, 371285126593915828, 371285127102481177, 371285127611728709, 371285128231871239, 371285128266623209, 371285128300222706, 371285128334263462, 371285128536937132, 371285128619611733]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362454462181303718, 362454487063317118⟩, ⟨1280081564517705668, 1280784337342577786⟩, true⟩

def words09 : List Nat := [371285129071782771, 371285129524508875, 371285129976366426, 371285129977741485, 371285129667069392, 371285129468540235, 371285129298828117, 371285129300203251, 371285128568415931, 371285127836937754]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk417
