import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598949863675666, 360598951704886473⟩, ⟨(-270410528014988792), (-270388219182930308)⟩, true⟩

def state01 : KState := ⟨⟨360613295648735949, 360613297492112488⟩, ⟨(-527880324833362411), (-527857977224052841)⟩, true⟩

def words00 : List Nat := [360583847061822029, 360583845580536115, 360583841004880361, 360583839534353027, 360583838063930086, 360583835798006450, 360583833656997473, 360583829631591169, 360583825606589379, 360583826330411631]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547792412512811, 360547794258034539⟩, ⟨645943082696346822, 645965468736957116⟩, true⟩

def words01 : List Nat := [360583831078364486, 360583835825830687, 360583838135131244, 360583840160072593, 360583841390689504, 360583842621229002, 360583843130548130, 360583843449438061, 360583843449643888, 360583841438209593]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360662875607627393, 360662877455295716⟩, ⟨(-1416794966129957444), (-1416772541611612844)⟩, true⟩

def words02 : List Nat := [360583840515291640, 360583843650290124, 360583849884099708, 360583856117257231, 360583859656501710, 360583860108571368, 360583860108759532, 360583859233779716, 360583860581572232, 360583864988528017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360648536822788335, 360648538672623736⟩, ⟨(-1159643219825059303), (-1159620756440494005)⟩, true⟩

def words03 : List Nat := [360583867515676174, 360583870042567391, 360583874633769109, 360583881751078744, 360583886940377451, 360583892129134734, 360583895722085159, 360583896230769318, 360583899834211264, 360583903437328018]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554215903231762, 360554217755214228⟩, ⟨532540164271144324, 532562666185002930⟩, true⟩

def words04 : List Nat := [360583905314604149, 360583905314832034, 360583904108706704, 360583901348032272, 360583898587628526, 360583894051845595, 360583891113000417, 360583890325145684, 360583889537350144, 360583886984528156]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360663670492656930, 360663672346791360⟩, ⟨(-1433045121089701773), (-1433022580537489781)⟩, true⟩

def words05 : List Nat := [360583885331923066, 360583885283363125, 360583886052486613, 360583886052714751, 360583885028117318, 360583881279714754, 360583877531686163, 360583878227514673, 360583882670578931, 360583887113199829]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579342663451803, 360579344519761005⟩, ⟨81703430087142362, 81726009709156930⟩, true⟩

def words06 : List Nat := [360583890003755893, 360583893012533934, 360583894947072323, 360583896881462574, 360583898023873203, 360583898307105869, 360583898307309202, 360583896844595388, 360583895382004475, 360583892433489951]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600780947685919, 360600782806144985⟩, ⟨(-303333787214003691), (-303311168948190155)⟩, true⟩

def words07 : List Nat := [360583895012282599, 360583897843873316, 360583899087742652, 360583901572353493, 360583903224404569, 360583904876336024, 360583909611017508, 360583912503187266, 360583913441673172, 360583914380087025]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360788850502138822, 360788852362756307⟩, ⟨(-3685976665830959155), (-3685954008746235233)⟩, true⟩

def words08 : List Nat := [360583918400560852, 360583924391807524, 360583930186945670, 360583935981479823, 360583938837859479, 360583941877090891, 360583947996248771, 360583954114792873, 360583963312557799, 360583974701217414]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360715317899898853, 360715319762693739⟩, ⟨(-2362669428894869844), (-2362646732627777372)⟩, true⟩

def words09 : List Nat := [360583984507587410, 360583994312891642, 360584005407068415, 360584018045832074, 360584029079918359, 360584040112817161, 360584048747657551, 360584054317908316, 360584061610618161, 360584068902595535]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk179
