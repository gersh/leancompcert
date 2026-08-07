import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568637897643155, 360568665929599897⟩, ⟨942560416532786381, 943812062349004191⟩, true⟩

def state01 : KState := ⟨⟨360599422468003575, 360599450508769647⟩, ⟨(-1092548178508193224), (-1091295950352225566)⟩, true⟩

def words00 : List Nat := [360582944262955795, 360582943947771606, 360582943832094109, 360582943889065572, 360582943889937292, 360582943758603046, 360582943398770128, 360582943267726862, 360582943232796942, 360582943483458395]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591087661403779, 360591115711037993⟩, ⟨(-541512479741992017), (-540259665268588591)⟩, true⟩

def words01 : List Nat := [360582943619470758, 360582943755580569, 360582943969162859, 360582944298025637, 360582944469512207, 360582944641131995, 360582944698186899, 360582944699123441, 360582944813642753, 360582944938283973]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593199262076513, 360593227320498960⟩, ⟨(-681174579080854089), (-679921183486414639)⟩, true⟩

def words02 : List Nat := [360582945097788372, 360582945263842914, 360582945293529036, 360582945323306755, 360582945324089010, 360582945279418793, 360582945496831681, 360582945714416419, 360582945735023757, 360582945891464371]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611191527777544, 360611219594999394⟩, ⟨(-1871135160193378821), (-1869881182650626231)⟩, true⟩

def words03 : List Nat := [360582946115508439, 360582946339832206, 360582946700670825, 360582946919315733, 360582946943241228, 360582946967254715, 360582947219321936, 360582947602733589, 360582948030946077, 360582948459355080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573573228789604, 360573601304917081⟩, ⟨616967138906947239, 618221705509209073⟩, true⟩

def words04 : List Nat := [360582948772662405, 360582948857961185, 360582948858733470, 360582948823920666, 360582948788856753, 360582948696635658, 360582948376238865, 360582947896422213, 360582947416440910, 360582947060102406]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360553857776117343, 360553885861021547⟩, ⟨1921339770109737339, 1922594917337011837⟩, true⟩

def words05 : List Nat := [360582946953011225, 360582946987376610, 360582946988207648, 360582946908261182, 360582946881301784, 360582946753251652, 360582946624948080, 360582946400944986, 360582946077370969, 360582945639094961]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593951035772607, 360593979129480437⟩, ⟨(-731434520003719800), (-730178790284295906)⟩, true⟩

def words06 : List Nat := [360582945200620962, 360582944990521611, 360582944980978088, 360582945068167022, 360582945069033189, 360582944932547506, 360582944567943638, 360582944381960413, 360582944236712031, 360582944404445539]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613076599823925, 360613104702427707⟩, ⟨(-1997137144500079614), (-1995880826092457062)⟩, true⟩

def words07 : List Nat := [360582944405292611, 360582944383833216, 360582944567801440, 360582944920554225, 360582945213017437, 360582945505629627, 360582945647715031, 360582945876418672, 360582946332882193, 360582946789641674]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585961247387443, 360585989358773500⟩, ⟨(-202556965061472097), (-201300065397531721)⟩, true⟩

def words08 : List Nat := [360582947303683153, 360582947590005973, 360582947732806588, 360582947875700661, 360582947876496087, 360582947917119385, 360582948020037002, 360582948123125048, 360582948123956649, 360582948158830947]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613922716996955, 360613950837211076⟩, ⟨(-2053455481664491609), (-2052197997629606835)⟩, true⟩

def words09 : List Nat := [360582948433412280, 360582948708276973, 360582949116205338, 360582949421839547, 360582949531910005, 360582949642048238, 360582949909680301, 360582950397438444, 360582950866491105, 360582951335728779]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661
