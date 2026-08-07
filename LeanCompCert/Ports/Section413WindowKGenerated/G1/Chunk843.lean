import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk843

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493208808535609, 362493315801412218⟩, ⟨(-680332177993790140), (-674242019109936536)⟩, true⟩

def state01 : KState := ⟨⟨362481822330016562, 362481929348990659⟩, ⟨279597408937984347, 285689767976055371⟩, true⟩

def words00 : List Nat := [371285317925424079, 371285317928350863, 371285317915924753, 371285317878345200, 371285317839595009, 371285317827628759, 371285317799222518, 371285317857536157, 371285317909215398, 371285317912245031]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504014323060573, 362504121368522286⟩, ⟨(-1591537777732138909), (-1585443185394134411)⟩, true⟩

def words01 : List Nat := [371285317947204744, 371285318023930418, 371285318239672122, 371285318268890053, 371285318271210272, 371285318255454890, 371285318360214403, 371285318445875617, 371285318670855453, 371285318897187813]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497328597413645, 362497435669318116⟩, ⟨(-1027771568959801987), (-1021674746831465925)⟩, true⟩

def words02 : List Nat := [371285319117971734, 371285319249736066, 371285319456843182, 371285319665429290, 371285319914401801, 371285320038205155, 371285320161240133, 371285320285287616, 371285320466767419, 371285320613800792]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477828803255125, 362477935901487895⟩, ⟨616802885700280174, 622901928228547520⟩, true⟩

def words03 : List Nat := [371285320850897002, 371285321089146034, 371285321326423921, 371285321390907011, 371285321480286912, 371285321571214135, 371285321673136057, 371285321676063722, 371285321590826703, 371285321506517876]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484590478994399, 362484697603470423⟩, ⟨46470747370131993, 52572003385439089⟩, true⟩

def words04 : List Nat := [371285321420942193, 371285321404843706, 371285321317300788, 371285321289092420, 371285321259931531, 371285321208567444, 371285320981193271, 371285320895870459, 371285320860648108, 371285320863735811]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481789631932389, 362481896783098762⟩, ⟨282776352550026028, 288879860029178244⟩, true⟩

def words05 : List Nat := [371285320858537202, 371285320855111546, 371285320963122926, 371285321020944406, 371285321120466333, 371285321221081266, 371285321297898434, 371285321300826726, 371285321190107912, 371285321153179715]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479986202389328, 362480093379647946⟩, ⟨434904904241975672, 441010612996439428⟩, true⟩

def words06 : List Nat := [371285321179984716, 371285321182913083, 371285321063257258, 371285320937775396, 371285320811142067, 371285320717353526, 371285320563072385, 371285320536401536, 371285320508703646, 371285320481852479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491769805741304, 362491877009441854⟩, ⟨(-559371027916129743), (-553263088123465023)⟩, true⟩

def words07 : List Nat := [371285320421925300, 371285320388352484, 371285320444684853, 371285320447613939, 371285320354097984, 371285320239201283, 371285320145379204, 371285320148665695, 371285320202574282, 371285320283542381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477564658861854, 362477671888984720⟩, ⟨639275967133452330, 645386136573460392⟩, true⟩

def words08 : List Nat := [371285320336770033, 371285320339701572, 371285320233912895, 371285320223096359, 371285320210790791, 371285320206995248, 371285320015316590, 371285319813845372, 371285319611203919, 371285319550278398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471879446492822, 362471986703062907⟩, ⟨1119136324939608749, 1125248726393854035⟩, true⟩

def words09 : List Nat := [371285319511374280, 371285319564387638, 371285319616305206, 371285319619234968, 371285319483880625, 371285319392781987, 371285319314465311, 371285319317401603, 371285319188576584, 371285319033944351]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk843
