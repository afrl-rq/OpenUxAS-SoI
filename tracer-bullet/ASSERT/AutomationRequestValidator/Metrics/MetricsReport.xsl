<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="2.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format"
                xmlns:mr="com.ge.aviation.systems.platform.assert.metricsreport"
                xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                xmlns:msxsl="urn:schemas-microsoft-com:xslt" exclude-result-prefixes="msxsl">
  <xsl:output method="html" version="4.0" encoding="UTF-8" indent="yes"/>
  <?altova_samplexml C:\DAILYBUILD\CheckReports\CheckXML.xml?>
  <!--GE Aviation Proprietary-->
  <!-- main -->
  <xsl:template match="/">
    <html>
      <head>
        <title>ASSERT Metrics Report</title>
        <link rel="stylesheet" type="text/css" href="default.css"/>
        <style TYPE="text/css">
          td.aname {width: 140}
          td.atype {width: 80}
          td.aconstraint {width: 140}
          td.summaryname {width: 50%}
          td.pname {width: 140}
          td.ptype {width: 80}
          td.punits {width: 80}
          td.puses {width: 80}
          td.pconstraints {width: 140}
          td.pentry {width: 80}
          table.meta_table{margin-left: -18px; font-size: 80%}
          p.margin-left {margin-left: -18px;}
        </style>
      </head>
      <!-- ====================================================================================
== Start Body
============================================================================================= -->
      <body id="bodyID" class="dtBODY">
        <!-- DoHeading -->
        <xsl:call-template name="DoHeading"/>
        <xsl:call-template name="DoTableOfContents"/>
        <div id="nstext">
          <xsl:for-each select ="/mr:metricsReportType/mr:Metric">
            <xsl:call-template name="DoCheckTable">
              <xsl:with-param name="mySectionNo" select="position()"/>
              <xsl:with-param name="myTableName" select="@name"/>
              <xsl:with-param name="myMetric" select="."/>
            </xsl:call-template>
          </xsl:for-each>
        </div>
      </body>
    </html>
  </xsl:template>
  <!-- ====================================================================================
== DoCheckTable - used for all three tables (Errors Table, Warnings Table, Tests that Passed Table)
========================================================================================== -->
  <xsl:template name="DoCheckTable">
    <xsl:param name="mySectionNo"/>
    <xsl:param name="myTableName"/>
    <xsl:param name="myMetric"/>
    <h4 class="dtH4">
      <a id="{$mySectionNo}">
        <xsl:value-of select="$mySectionNo"/>
      </a>
      <xsl:text> </xsl:text>
      <!--<xsl:value-of select="$myTableName"/>-->
    </h4>
    <div id="metricdiv">
      <h3>
        <xsl:value-of select ="substring-before($myMetric/@name, ' of project, ')"/>
      </h3>
      <h4>
        <xsl:value-of select ="concat('Project ',substring-after($myMetric/@name, ' of project, '))"/>
      </h4>
      <xsl:text>Timestamp </xsl:text>
      <xsl:value-of select ="$myMetric/@dateTime"/>
      <br/>
      <xsl:text>Elapsed Time Total </xsl:text>
      <xsl:variable name ="times">
        <xsl:for-each select ="$myMetric/descendant::*/@time">
		  <xsl:element name = "hourTime">
  			<xsl:if test="substring-before(., 'H') != ''">
 			  <xsl:value-of select="translate(substring-before(., 'H'), 'PT','')"/>
			</xsl:if>
  			<xsl:if test="substring-before(., 'H') = ''">
			  <xsl:value-of select="0"/>
			</xsl:if>
		  </xsl:element>
		  <xsl:variable name="afterHour">
			<xsl:if test="substring-before(., 'H') != ''">
			  <xsl:value-of select="substring-after(., 'H')"/>
			</xsl:if>
			<xsl:if test ="substring-before(.,'H') = ''">
			  <xsl:value-of select="."/>
			</xsl:if>
		  </xsl:variable>
		  <xsl:element name="minTime">
   			<xsl:if test="substring-before($afterHour, 'M') != ''">
			  <xsl:value-of select = "translate(substring-before($afterHour, 'M'), 'PT', '')"/>
			</xsl:if>
  			<xsl:if test="substring-before($afterHour, 'M') = ''">
			  <xsl:value-of select="0"/>
			</xsl:if>
		  </xsl:element>
		  <xsl:variable name="afterMin">
		    <xsl:if test="substring-before($afterHour, 'M') != ''">
			  <xsl:value-of select = "substring-after($afterHour, 'M')"/>
			</xsl:if>
			<xsl:if test="substring-before($afterHour, 'M') = ''">
			  <xsl:value-of select = "$afterHour"/>
			</xsl:if>
		  </xsl:variable>
          <xsl:element name ="secTime">
            <xsl:value-of select="translate(substring-before($afterMin, 'S'),'PT','')"/>
          </xsl:element>
        </xsl:for-each>
      </xsl:variable>
      <xsl:variable name ="times2" select ="msxsl:node-set($times)"/>
      <xsl:value-of select ="format-number(sum($times2/hourTime)*60*60 + sum($times2/minTime)*60 + sum($times2/secTime), '#####0.#####')"/>
      <xsl:text> seconds</xsl:text>
      <br/>
      <xsl:variable name ="submetrics">
        <xsl:for-each select ="$myMetric/descendant::*[@xsi:type ='RatioMetricType']">
          <xsl:copy-of select ="."/>
        </xsl:for-each>
      </xsl:variable>
      <xsl:for-each select ="msxsl:node-set($submetrics)/*[not(@name = preceding::*/@name)]">
        <xsl:variable name ="name" select ="@name"/>
        <xsl:value-of select ="$name"/>
        <xsl:text> - </xsl:text>
        <xsl:variable name ="conseq" select ="sum($myMetric/descendant::*[@xsi:type ='RatioMetricType' and @name = $name]/mr:Consequent)"/>
        <xsl:variable name ="ante" select ="sum($myMetric/descendant::*[@xsi:type ='RatioMetricType' and @name = $name]/mr:Antecedent)"/>
        <xsl:choose>
          <xsl:when test ="not($ante = $conseq)">
            <span class="bold-red">
              <xsl:value-of select ="$ante"/>
            </span>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select ="$ante"/>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:text> of </xsl:text>
        <xsl:value-of select ="$conseq"/>
        <xsl:value-of select ="concat(' ', @unit)"/>
        <xsl:text> - </xsl:text>
        <xsl:choose>
          <xsl:when test ="number($conseq) = 0 ">
            <xsl:text>NaN</xsl:text>
          </xsl:when>
          <xsl:when test ="not($ante = $conseq)">
            <span class="bold-red">
              <xsl:value-of select ="format-number(($ante div $conseq) * 100, '0.##')"/><xsl:text>%</xsl:text>
            </span>            
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select ="format-number(($ante div $conseq) * 100, '0.##')"/>
            <xsl:text>%</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
        <br/>
      </xsl:for-each>
      <xsl:for-each select ="$myMetric/*[@xsi:type = 'ElapsedTimeMetricType']">
        <div id="timemetricdiv">
          <xsl:apply-templates select ="."/>
        </div>
      </xsl:for-each>
      <xsl:apply-templates select ="$myMetric/*[not(@xsi:type = 'ElapsedTimeMetricType')]"/>
    </div>
    <br/>
  </xsl:template>

  <xsl:template match="*[@xsi:type = 'AggregateMetric']">
    <xsl:variable name ="myMetric" select ="."/>
    <div id="submetricdiv">
      <h4>
        <xsl:value-of select ="@name"/>
      </h4>
      <xsl:text>Timestamp </xsl:text>
      <xsl:value-of select ="$myMetric/@dateTime"/>
      <br/>
      <xsl:if test ="count(SubMetric) >  0">
        <xsl:text>Elapsed Time Total </xsl:text>
        <xsl:variable name ="times">
          <xsl:for-each select ="$myMetric/descendant::*/@time">
		  	<xsl:element name = "hourTime">
			  <xsl:if test="substring-before(.,'H') != ''">
		        <xsl:value-of select="translate(substring-before(., 'H'), 'PT','')"/>
			  </xsl:if>
			  <xsl:if test = "substring-before(.,'H') = ''">
			    <xsl:value-of select="0"/>
			  </xsl:if>
		    </xsl:element>
			<xsl:variable name = "remaining">
				<xsl:if test="substring-before(., 'H') != ''">
				  <xsl:value-of select="substring-after(.,'H')"/>
				</xsl:if>
				<xsl:else>
					<xsl:value-of select="."/>
				</xsl:else>
			</xsl:variable>
			<xsl:element name="minTime">
			  <xsl:if test="substring-before($remaining,'M') != ''">
		        <xsl:value-of select = "translate(substring-before($remaining, 'M'), 'PT', '')"/>
			  </xsl:if>
			  <xsl:if test="substring-before($remaining,'M') = ''">
			    <xsl:value-of select = "0"/>
			  </xsl:if>
			</xsl:element>
			<xsl:variable name = "remaining1">
				<xsl:if test="substring-before($remaining, 'M') != ''">
				  <xsl:value-of select="substring-after($remaining,'M')"/>
				</xsl:if>
				<xsl:else>
					<xsl:value-of select="$remaining"/>
				</xsl:else>
			</xsl:variable>
            <xsl:element name ="secTime">
              <xsl:value-of select="translate((substring-before($remaining1, 'S'),'PT','')"/>
            </xsl:element>
          </xsl:for-each>
        </xsl:variable>
        <xsl:variable name ="times2" select ="msxsl:node-set($times)"/>
        <xsl:value-of select ="format-number(sum($times2/hourTime)*60*60 + sum($times2/minTime)*60 + sum($times2/secTime), '#####0.#####')"/>
        <xsl:text> seconds</xsl:text>
        <br/>
        <xsl:variable name ="submetrics">
          <xsl:for-each select ="$myMetric/descendant::*[@xsi:type ='RatioMetricType']">
            <xsl:copy-of select ="."/>
          </xsl:for-each>
        </xsl:variable>
        <xsl:for-each select ="msxsl:node-set($submetrics)/*[not(@name = preceding::*/@name)]">
          <xsl:variable name ="name" select ="@name"/>
          <xsl:value-of select ="$name"/>
          <xsl:text> - </xsl:text>
          <xsl:variable name ="conseq" select ="sum($myMetric/descendant::*[@xsi:type ='RatioMetricType' and @name = $name]/mr:Consequent)"/>
          <xsl:variable name ="ante" select ="sum($myMetric/descendant::*[@xsi:type ='RatioMetricType' and @name = $name]/mr:Antecedent)"/>
          <xsl:choose>
            <xsl:when test ="not($ante = $conseq)">
              <span class="bold-red">
                <xsl:value-of select ="$ante"/>
              </span>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select ="$ante"/>
            </xsl:otherwise>
          </xsl:choose>
          <xsl:text> of </xsl:text>          
          <xsl:value-of select ="$conseq"/>
          <xsl:value-of select ="concat(' ', @unit)"/>
          <xsl:text> - </xsl:text>
          <xsl:choose>
            <xsl:when test ="number($conseq) = 0 ">
              <xsl:text>NaN</xsl:text>
            </xsl:when>
            <xsl:when test ="not($ante = $conseq)">
              <span class="bold-red"><xsl:value-of select ="format-number(($ante div $conseq) * 100, '0.##')"/></span>
              <xsl:text>%</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select ="format-number(($ante div $conseq) * 100, '0.##')"/><xsl:text>%</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
          
          <br/>
        </xsl:for-each>
      </xsl:if>
      <xsl:apply-templates select ="$myMetric/*"/>
    </div>
    <br/>
  </xsl:template>
  <xsl:template match="*[@xsi:type = 'ElapsedTimeMetricType']">
    <xsl:variable name ="myMetric" select ="."/>
    <!--<div id="timemetricdiv">-->
    <!--<h5>-->
    <xsl:value-of select ="@name"/>
    <xsl:text> Elapsed Time - </xsl:text>
    <xsl:value-of select ="translate(@time,'PTS','')"/>
    <xsl:text> seconds</xsl:text>
    <br/>
    <xsl:apply-templates select ="mr:Error"/>
    <!--</h5>-->
    <!--</div>-->
    <!--<br/>-->
  </xsl:template>
  <xsl:template match="*[@xsi:type = 'RatioMetricType']">
    <!--<div id="ratiometricdiv">-->
    <!--<h5>-->
    <xsl:value-of select ="@name"/>
    <xsl:text> Ratio - </xsl:text>
    <xsl:variable name ="ante" select ="mr:Antecedent"/>
    <xsl:variable name ="conseq" select ="mr:Consequent"/>
    <xsl:choose>
      <xsl:when test ="not($ante = $conseq)">
        <span class="bold-red"><xsl:value-of select ="$ante"/></span>
      </xsl:when>
      <xsl:otherwise>
        <xsl:value-of select ="$ante"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text> of </xsl:text>
    <xsl:value-of select ="$conseq"/>
    <xsl:value-of select ="concat(' ', @unit)"/>
    <xsl:text> - </xsl:text>
    <xsl:choose>
      <xsl:when test ="number($conseq) = 0 ">
        <xsl:text>NaN</xsl:text>
      </xsl:when>
      <xsl:when test ="$ante = $conseq">
        <xsl:value-of select ="format-number(($ante div $conseq) * 100, '0.##')"/>
        <xsl:text>%</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <span class="bold-red">
          <xsl:value-of select ="format-number(($ante div $conseq) * 100, '0.##')"/>
          <xsl:text>%</xsl:text>
        </span>
      </xsl:otherwise>
    </xsl:choose>
    <br/>
    <xsl:apply-templates select ="mr:Error"/>
    <!--</h5>-->
    <!--</div>-->
    <!--<br/>-->
  </xsl:template>

  <xsl:template match ="mr:Error">
    <span class="bold-red">
      <xsl:value-of select ="@severity"/>
      <xsl:text>:  </xsl:text>
      <xsl:value-of select ="@message"/>
    </span>
    <br/>
  </xsl:template>


  <!-- =================================================================
==        DoTableOfContents
==================================================================== -->
  <xsl:template name="DoTableOfContents">
    <!-- table of contents -->
    <div style="font-size:120%;margin-left:10px;">
      <br/>
      <div style="font-size:150%;">
        Table of Contents
      </div>
      <xsl:for-each select ="/mr:metricsReportType/mr:Metric">
        <xsl:element name ="a">
          <xsl:attribute name ="href">
            <xsl:value-of select ="concat('#',position())"/>
          </xsl:attribute>
          <xsl:value-of select ="@name"/>
        </xsl:element>
        <xsl:text>   -   </xsl:text>
        <xsl:value-of select ="@dateTime"/>
        <br/>
      </xsl:for-each>
      <br/>
    </div>
    <hr/>
    <!-- end table of contents -->
  </xsl:template>
  <!-- ====================================================================================
== DoHeading - prints the heading at the top of the output document
====================================================================================== -->
  <xsl:template name="DoHeading">
    <div id="nsbanner">
      <!--<div id="bannerrow1">
        <table class="bannerparthead" cellspacing="0">
          <tr id="hdr">
            <td class="runninghead"> </td>
            <td class="product"/>
          </tr>
        </table>
      </div>-->
      <div id="TitleRow">
        <h1 class="dtH1" style="text-transform: uppercase;">ASSERT Metrics Report</h1>
        <h2 class="dtH1">
          <xsl:value-of select="/mr:metricsReportType/mr:ReportingTool/@name"/>
        </h2>
      </div>
      <div id="bannerrow1">
        <table class="bannerparthead" cellspacing="0">
          <tr>
            <td style="width:160px">Version: </td>
            <td>
              <xsl:value-of select="/mr:metricsReportType/mr:ReportingTool/@version"/>
            </td>
          </tr>
          <tr>
            <td style="width:160px"> </td>
            <td> </td>
          </tr>
          <tr>
            <td style="width:160px">
              <u>Compatible Tool Versions</u></td><td> </td>
          </tr>
          <xsl:for-each select ="/mr:metricsReportType/mr:CompatibleTool">
            <tr>
              <td style="width:160px">
                <xsl:value-of select ="@name"/>
              </td>
              <td>
                <xsl:value-of select ="@version"/>
              </td>
            </tr>
          </xsl:for-each>
        </table>
        <br/>
        <br/>
      </div>
    </div>
    <!-- end  div nsbanner -->
  </xsl:template>
</xsl:stylesheet>
