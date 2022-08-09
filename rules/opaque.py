import xml.etree.ElementTree as ET
import sys

ET.register_namespace('', "http://www.w3.org/2000/svg")
ET.register_namespace('xlink', "http://www.w3.org/1999/xlink")

diagram = ET.parse(sys.argv[1])
root = diagram.getroot()
root.insert(0, ET.Element('rect', {'width': '100%', 'height' : '100%', 'fill' : 'white'}))
diagram.write(sys.argv[1])