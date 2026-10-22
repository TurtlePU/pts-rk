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
for needle in ["Hilbert", "modus ponens", "Bunder", "finite typed basis"] {
    guard text.contains(needle) else { fatalError("Missing required content: \(needle)") }
}
let urls = pages.flatMap { $0.annotations.compactMap { $0.url } }
let remote = pages.flatMap { $0.annotations.compactMap { ($0.action as? PDFActionRemoteGoTo)?.url } }
let links = urls + remote
let sourceLinks = links.filter { $0.pathExtension == "v" }
guard sourceLinks.count >= 4 else { fatalError("Missing formalization badges") }
for link in sourceLinks {
    let source = sourceDir.appendingPathComponent(link.lastPathComponent)
    guard FileManager.default.fileExists(atPath: source.path) else {
        fatalError("Badge source missing: \(source.path)")
    }
}
guard links.contains(where: { $0.absoluteString.contains("10.2168/LMCS-4(1:1)2008") }) else {
    fatalError("Missing Bunder--Dekkers DOI link")
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
print("PASS: pages=\(doc.pageCount), source badges=\(sourceLinks.count), links=\(links.count)")
