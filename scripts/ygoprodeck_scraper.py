import requests
import json

f = open("json/ygoprodeck_card_info.json", "w")
url = "https://db.ygoprodeck.com/api/v7/cardinfo.php?misc=yes"
res = requests.get(url)
data = json.dumps(res.json(), indent=4)
f.write(data)
f.close()