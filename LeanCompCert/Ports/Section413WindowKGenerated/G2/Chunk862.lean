import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk862

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360549673375193216, 360549722054016483⟩, ⟨2800635503441011803, 2803469205272654759⟩, true⟩

def state01 : KState := ⟨⟨360556281440450361, 360556330130971751⟩, ⟨2230991082561422977, 2233825792830344995⟩, true⟩

def words00 : List Nat := [360582244522336314, 360582244280851784, 360582244106634578, 360582243913481160, 360582243720254027, 360582243398032042, 360582242940999628, 360582242441788885, 360582241942225581, 360582241577356514]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360548233206034603, 360548281908387968⟩, ⟨2924891321860712438, 2927727052222203324⟩, true⟩

def words01 : List Nat := [360582241277914820, 360582240899105266, 360582240520045364, 360582240241737600, 360582240030942905, 360582239763619211, 360582239496161478, 360582239144953107, 360582238773221927, 360582238380809938]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360547973342031922, 360548022056063911⟩, ⟨2947313236544717672, 2950149973896024030⟩, true⟩

def words02 : List Nat := [360582237987981592, 360582237702252748, 360582237358429271, 360582236930626425, 360582236502629017, 360582236039838983, 360582235680745827, 360582235368942525, 360582235057034586, 360582234626792150]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558026765719330, 360558075491466060⟩, ⟨2080288099578017406, 2083125847151150764⟩, true⟩

def words03 : List Nat := [360582234231039851, 360582233930357599, 360582233629335689, 360582233292267315, 360582232820614037, 360582232234776317, 360582231648714568, 360582231167969968, 360582230754557037, 360582230475779038]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562699028247149, 360562747765798297⟩, ⟨1677241763957307346, 1680080529599572098⟩, true⟩

def words04 : List Nat := [360582230196802444, 360582229811885658, 360582229433884408, 360582229190557181, 360582228946906999, 360582228648581099, 360582228279065323, 360582227794737592, 360582227310183339, 360582226960344379]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360562987799030814, 360563036548261927⟩, ⟨1652327488327313335, 1655167261425765801⟩, true⟩

def words05 : List Nat := [360582226735510733, 360582226531680379, 360582226327719418, 360582226056638215, 360582225824329511, 360582225519579459, 360582225214459304, 360582225043851434, 360582224889773015, 360582224668612331]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585547615612604, 360585596376569076⟩, ⟨(-293817020449592980), (-290976235865329100)⟩, true⟩

def words06 : List Nat := [360582224447190020, 360582224222598296, 360582224108969284, 360582224120017085, 360582224121173290, 360582224014317405, 360582223772808605, 360582223644351950, 360582223519878827, 360582223560259247]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558213272793855, 360558262045557280⟩, ⟨2064445188990864236, 2067286992219043090⟩, true⟩

def words07 : List Nat := [360582223561364555, 360582223524934905, 360582223488277359, 360582223401881972, 360582223382663609, 360582223230225243, 360582223077655007, 360582222857983929, 360582222532698916, 360582222256408220]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564743600851089, 360564792385309774⟩, ⟨1500970518892769996, 1503813331247500762⟩, true⟩

def words08 : List Nat := [360582221979716174, 360582221743129202, 360582221510057658, 360582221209971642, 360582220909680732, 360582220575892025, 360582220312777533, 360582220184072680, 360582220055254966, 360582219819905295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360601379156994515, 360601427953171400⟩, ⟨(-1660512273139295094), (-1657668449564951206)⟩, true⟩

def words09 : List Nat := [360582219618947020, 360582219552532520, 360582219552092831, 360582219581464814, 360582219582616977, 360582219479663170, 360582219406378671, 360582219519155557, 360582219742736067, 360582219966594594]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk862
