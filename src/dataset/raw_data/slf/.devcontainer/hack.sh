#!/usr/bin/env bash

### HACK - workaround ubuntu libc6 version number bug see: https://forum.odroid.com/viewtopic.php?p=344373

mv /bin/uname /bin/uname.orig
tee -a /bin/uname <<EOF
#!/bin/bash
if [[ \$1 == "-r" ]]; then
echo '4.9.250';
exit
else
uname.orig \$1
fi
EOF

chmod 755 /bin/uname
### END HACK
