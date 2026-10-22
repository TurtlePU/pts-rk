import Foundation
import AppKit
import PDFKit

let pdfPath = CommandLine.arguments[1]
let out = CommandLine.arguments[2]
let sourceDir = URL(fileURLWithPath: pdfPath).deletingLastPathComponent()
guard let doc = PDFDocument(url: URL(fileURLWithPath: pdfPath)) else {
    fatalError("Unreadable PDF")
}
let pages = (0..<doc.pageCount).map { doc.page(at: $0)! }
let text = pages.map { $0.string ?? "" }.joined(separator: "\n")
for needle in ["Hilbert", "modus ponens", "Bunder", "QIIRT", "tyOf", "TyExact",
               "External mathematical completeness", "Metamath Zero",
               "h_universe", "h_apply", "h_convert", "coreS", "sortK2l", "sortS"] {
    guard text.lowercased().contains(needle.lowercased()) else {
        fatalError("Missing required content: \(needle)")
    }
}
guard let appendix = pages.firstIndex(where: {
    ($0.string ?? "").contains("Complete MM0 source")
}) else { fatalError("Missing MM0 appendix") }
guard (1...3).contains(doc.pageCount - appendix) else {
    fatalError("Full MM0 appendix exceeds three pages")
}
let appendixText = pages[appendix...].map { $0.string ?? "" }.joined(separator: "\n")
guard appendixText.contains("strict sort nat"), appendixText.contains("ENDHILBERT") else {
    fatalError("Incomplete source listing")
}
let bodyText = pages[..<appendix].map { $0.string ?? "" }.joined(separator: "\n")
guard bodyText.contains("4.1 A Metamath Zero specification"),
      bodyText.contains("h_apply"), bodyText.contains("h_type") else {
    fatalError("Missing Section 4 source excerpt")
}
let urls = pages.flatMap { $0.annotations.compactMap { $0.url } }
let remote = pages.flatMap { $0.annotations.compactMap { ($0.action as? PDFActionRemoteGoTo)?.url } }
let links = urls + remote
let sourceLinks = links.filter { $0.pathExtension == "v" }
guard sourceLinks.count == 19 else { fatalError("Missing formalization badges") }
for link in sourceLinks {
    guard FileManager.default.fileExists(atPath:
        sourceDir.appendingPathComponent(link.lastPathComponent).path) else {
        fatalError("Badge source missing: \(link)")
    }
}
for needle in ["10.2168/LMCS-4(1:1)2008", "tt-qiirt_cpp2026.pdf",
               "10.1007/978-3-030-53518-6_5", "/mm0.md", "CombinatoryPTS-rk.mm0",
               "CombinatoryPTS-rk-examples.mm1"] {
    guard links.contains(where: { $0.absoluteString.contains(needle) }) else {
        fatalError("Missing reference/source link: \(needle)")
    }
}
try text.write(toFile: out + "/pdf-text.txt", atomically: true, encoding: .utf8)
try links.map { $0.absoluteString }.joined(separator: "\n").write(
    toFile: out + "/pdf-links.txt", atomically: true, encoding: .utf8)
for index in 0..<doc.pageCount {
    let page = pages[index]
    let bounds = page.bounds(for: .mediaBox)
    let img = page.thumbnail(of: NSSize(width: bounds.width * 1.25, height: bounds.height * 1.25), for: .mediaBox)
    guard let data = img.tiffRepresentation, let bitmap = NSBitmapImageRep(data: data),
          let png = bitmap.representation(using: .png, properties: [:]) else {
        fatalError("Page rendering failed")
    }
    try png.write(to: URL(fileURLWithPath: out + "/page-\(index + 1).png"))
}
print("PASS: pages=\(doc.pageCount), appendix=\(doc.pageCount - appendix) pages, source badges=\(sourceLinks.count), links=\(links.count)")
