#!/bin/bash

#
# Script collected by daleif (@math.au.dk), 2023 with ideas from mato@au.dk
# Long install phrase provided by AUIT
#


############################################################
# Help                                                     #
############################################################
Help()
{
    # Display Help
    cat <<EOF
Adding an AU smb printer via CLI.

Syntax: install_printer [-P|-L|-h]
options:
-P name      Printer to be added.
-L location  Where the printer is located
-N           Do not check that the printer exists using smbclient
-l           List the printers using smbclient
-h           Print this Help.

If the -P or -L values are not given we instead prompt for them.
Note that we will use the generic driver, this can be changed manually afterwards.

-l can be prepended by ' | grep 1530 ' to find all printers in 1530

Easter egg: if the printer name is just a building number, the
programme lists the printers in that building.

EOF

}

# check setup

# credit https://saturncloud.io/blog/how-to-check-if-a-program-exists-from-a-bash-script/
if ! which smbclient >/dev/null; then
    cat <<EOF

smbclient is not found, you can install it via:

sudo apt install smbclient

EOF
    exit
fi
if ! which klist >/dev/null; then
    cat <<EOF

klist (kerberos tool) is not found. We need kerberos user tools in
order ease communication with the print server.  Please install at
least krb5-user:

sudo apt install krb5-user

or similar.

EOF
    exit
fi

if ! which lpadmin >/dev/null; then
    cat <<EOF

lpadmin is not found. That is rather strange as it is normally
installed by default. Please install cups-client:

sudo apt install cups-client

EOF
    exit
fi


PRINTER=""
LOCATION=""
NO_CHECK=false
LIST_PRINTERS=false

# Get the options
while getopts ":hP:L:Nl" option; do
   case $option in
      h) # display Help
         Help
         exit;;
      P) # specify printer to install
	  PRINTER=$OPTARG;;
      L) # specify printer to install
	  LOCATION=$OPTARG;;
      N)
	  NO_CHECK=true;;
      l)
	  LIST_PRINTERS=true;;
      \?) # Invalid option
          echo "Error: Invalid option"
	  echo
	  Help
          exit;;
   esac
done


# check that the kerberos ticket is valid and from AU
if klist -s && klist -l | grep -iq "UNI.AU.DK" 
then
    # echo "AU kerberos ticket is valid, proceeding"
    :
else
    cat <<EOF;

Did not find a valid AU Kerberos ticket. We need a ticket to ease
communication with the printserver (to avoid username and password all
the time). Please run the following command to create an AU ticket:

kinit auAUID@UNI.AU.DK

with your own auAUID (remember the au in front). Note that the
uppercase "@UNI.AU.DK" is REQUIRED, lowercase does not work. 
NB: 'kinit' will ask for your AU password.

Afterwards you can run 'klist -l' to see if it specifies something. This
will also tell you for how long your ticket is valid.

Once a ticket is availalbe you can rerun "$0".

Please note that the ticket is only used for the installation via this
programme. Specifying username and password when printing is handled
elsewhere.

EOF
    
    exit
    
fi


KRB_CACHE_LOCATION=$(klist -l | grep -i "UNI.AU.DK" | awk -F " " '{print $3}' | sed 's/^.*FILE://' )
SMB_CLIENT_CMD="smbclient --use-kerberos=required --use-krb5-ccache=$KRB_CACHE_LOCATION -L prt11.uni.au.dk"

if [[ "$LIST_PRINTERS" == true ]]
then
     $SMB_CLIENT_CMD | grep -vi disk | grep -vi ipc
    exit
fi


# prompt if missing data
if [[ -z $PRINTER  || -z $LOCATION  ]]
then
    echo "Missing options, prompting instead (easter egg: list only the building number to get a list of printers in that building)"
    if [[ -z $PRINTER ]]
    then
	read -p 'Printer name: ' PRINTER
	if [[ -z $PRINTER ]]
	then
	    echo "Printer is required"
	    exit
	fi
    fi
    A=$PRINTER
    # use printer name as default location
    A=$(echo $A | sed 's/-/./g' | sed 's/\.[^.]*//2g')
    if [[ -z $LOCATION ]]
    then
	read -p "Location [$A]: " LOCATION
	if [[ -z $LOCATION  ]]
	then
	    LOCATION=$A
	fi
    fi
fi

# check to see if the print server knowns the printer
if [[ "$NO_CHECK" == false ]]
then

    LIST=$($SMB_CLIENT_CMD | grep -c -i "$PRINTER")
    PRINTER_CHECK=$($SMB_CLIENT_CMD | grep -i "$PRINTER" | awk -F " " '{print $1}' )
    if (( $LIST < 1 ))
    then
	echo "Printer '$PRINTER' is not known to the print server, exiting"
	BUILDING=$(echo "$PRINTER" | awk -F "-" '{print $1}')
	echo "Available printers in $BUILDING:"
	$SMB_CLIENT_CMD | grep "$BUILDING"
	exit
    elif [[ $LIST > 1 || "$PRINTER_CHECK" != "$PRINTER" ]]
    then
	echo "'$LIST' results for '$PRINTER', please be more specific"
	BUILDING=$(echo "$PRINTER" | awk -F "-" '{print $1}')
	echo "Available printers in $BUILDING:"
	$SMB_CLIENT_CMD | grep "$BUILDING"
	exit
    else
	echo "Printer ($PRINTER) is known to the print server, proceeding"
    fi

fi


# cat <<EOF

# Will install printer via sudo with the following command:

# lpadmin -p "$PRINTER" -v "smb://UNI/prt11.uni.au.dk/$PRINTER" -L "$LOCATION" -m "drv:///sample.drv/generic.ppd" -o auth-info-required=username,password -o PageSize=A4 -E

# EOF

read -r -p "Confirm to proceed [Y/n]" response
response=${response,,} # tolower
if [[ $response =~ ^(y| ) ]] || [[ -z $response ]];
then

    #set -x
    echo
    lpadmin -p "$PRINTER" -v "smb://UNI/prt11.uni.au.dk/$PRINTER" -L "$LOCATION" -m "drv:///sample.drv/generic.ppd" -o auth-info-required=username,password -o PageSize=A4 -E
    echo
    #set +x
    echo -e "\n\nInstalled the following printer using a *generic driver*:"
    $SMB_CLIENT_CMD | grep -i "$PRINTER"
    echo "The driver can be changed manually in Printers GUI." 
    echo "Duplex must also be selected in Printers GUI"

else

    echo "Printer installation aborted"
    
fi



#Ændret printer-check da den godtog fx "1521" som printer findes
#Tilføjet at den viser printere i bygningen, hvis printer-check fejler. 
#Tilføjet at den viser den installerede printer ud til sidst med model, så det er nemmere at finde driver efterfølgende. 
# Added checks for smbclient, klist and lpadmin
# Added checks for valid AU kerberos ticket
# Fixed bug where a building with just one printer could trigger installation. Printer name need to match eactly
# Removed the use of sudo to run the lpadmin command
# Changed how KRB_CACHE_LOCATION finds the cache file
